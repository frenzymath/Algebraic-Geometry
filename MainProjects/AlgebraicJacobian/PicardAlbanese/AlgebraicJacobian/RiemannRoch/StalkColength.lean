/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.ChartColength
import AlgebraicJacobian.RiemannRoch.DivisorSheafZero

/-!
# The stalk colength dictionary (the pointwise face of SB-3)

For the curve bundle `X/K` and a closed point `z` of an affine chart `V`, this file computes
the `K`-colength of the stalk quotient by the germ of a nonzero chart section `f`:

`finrank K (𝒪_{X,z} ⧸ (germ_z f)) = count p_z (factors (f)) · [κ(z) : K]`,

the **pointwise** form of the chart colength dictionary (`finrank_quotient_span_section`
aggregates these along the support).  The stalk quotient is the chart-INDEPENDENT local model
into which the glued colength module of a divisor adaptation decomposes
(`AlgebraicJacobian.Picard.DivisorFamilyFieldCRT`): a closed point seen by two charts is seen
with the *same* stalk, which is what resolves the cross-chart double counting of the
Mayer–Vietoris colength↔degree identity.

* `Scheme.stalkOverAlgebra` — the `K`-algebra structure on the stalk `𝒪_{X,z}` through the
  structure morphism `K → Γ(X, ⊤) → 𝒪_{X,z}` (the stalk face of `Scheme.overSectionsAlgebra`
  and `Scheme.residueOverAlgebraMap`; deliberately not a global instance, house rule).
* `Scheme.germAlgHom` — the germ map `Γ(X, V) →ₐ[K] 𝒪_{X,z}` as a `K`-algebra homomorphism,
  with the scalar tower `Scheme.stalkOverAlgebra_isScalarTower`.
* `span_singleton_eq_maximalIdeal_pow_count` — in a local Dedekind domain (a DVR), a nonzero
  principal ideal is the count-th power of the maximal ideal.
* `moduleFinite_stalkQuot_span_germ` / `finrank_stalkQuot_span_germ` — the dictionary:
  transported to the chart along `quotPowLinearEquiv` (`B ⧸ p^e ≃ₗ[K] 𝒪_z ⧸ m^e`), where the
  per-prime collapse `finrank_quotient_pow_atPrime` and the residue leg
  `finrank_quotient_primeIdealOf` are landed.
-/

set_option autoImplicit false

universe u

open CategoryTheory
open Module (finrank)
open UniqueFactorizationMonoid IsLocalRing

namespace AlgebraicGeometry

/-! ## The `K`-algebra structure on stalks of a scheme over `K` -/

section StalkAlgebra

variable (K : Type u) [CommRing K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]

/-- The `K`-algebra structure on the stalk `𝒪_{X,z}` of a scheme over `Spec K`: restriction
of scalars along `K → Γ(X, ⊤) → 𝒪_{X,z}` (the stalk face of `Scheme.overSectionsAlgebra`; the
composite with the residue map is `Scheme.residueOverAlgebraMap`).  Deliberately **not** a
global instance (house rule for `Scheme.overModule`); activate with
`attribute [local instance] Scheme.stalkOverAlgebra`, and note that the `finrank` statements
below mention it, so consumers must activate the same instance. -/
@[reducible] noncomputable def Scheme.stalkOverAlgebra (z : X) :
    Algebra K (X.presheaf.stalk z) :=
  ((X.presheaf.germ ⊤ z trivial).hom.comp (X.overAlgebraMap K ⊤)).toAlgebra

attribute [local instance] Scheme.overSectionsAlgebra Scheme.stalkOverAlgebra

/-- The germ of the chart structure map is the stalk structure map: the `K`-structures of
`Scheme.overSectionsAlgebra` and `Scheme.stalkOverAlgebra` are compatible along germs from
any chart. -/
lemma Scheme.germ_algebraMap_overSections {V : X.Opens} {z : X} (hz : z ∈ V) (c : K) :
    (X.presheaf.germ V z hz).hom (algebraMap K Γ(X, V) c)
      = algebraMap K (X.presheaf.stalk z) c := by
  rw [Scheme.algebraMap_overSectionsAlgebra]
  change (X.presheaf.germ V z hz).hom (X.overAlgebraMap K V c)
      = (X.presheaf.germ ⊤ z trivial).hom (X.overAlgebraMap K ⊤ c)
  rw [← X.overAlgebraMap_apply_res K (homOfLE (le_top : V ≤ ⊤)).op c]
  exact X.presheaf.germ_res_apply (homOfLE le_top) z hz _

/-- The germ map at `z ∈ V` as a `K`-algebra homomorphism (`Scheme.overSectionsAlgebra` on
the sections, `Scheme.stalkOverAlgebra` on the stalk). -/
noncomputable def Scheme.germAlgHom {V : X.Opens} {z : X} (hz : z ∈ V) :
    Γ(X, V) →ₐ[K] X.presheaf.stalk z :=
  AlgHom.mk' (X.presheaf.germ V z hz).hom fun c s => by
    simp only [Algebra.smul_def, map_mul, Scheme.germ_algebraMap_overSections]

@[simp]
lemma Scheme.germAlgHom_apply {V : X.Opens} {z : X} (hz : z ∈ V) (s : Γ(X, V)) :
    Scheme.germAlgHom K hz s = (X.presheaf.germ V z hz).hom s :=
  rfl

/-- The stalk `K`-structure is the chart `K`-structure composed with the germ: the scalar
tower for the section-to-stalk algebra `TopCat.Presheaf.algebra_section_stalk`. -/
theorem Scheme.stalkOverAlgebra_isScalarTower {V : X.Opens} {z : X} (hz : z ∈ V) :
    letI : Algebra Γ(X, V) (X.presheaf.stalk z) := X.presheaf.algebra_section_stalk ⟨z, hz⟩
    IsScalarTower K Γ(X, V) (X.presheaf.stalk z) := by
  letI : Algebra Γ(X, V) (X.presheaf.stalk z) := X.presheaf.algebra_section_stalk ⟨z, hz⟩
  refine IsScalarTower.of_algebraMap_eq fun c => ?_
  exact (Scheme.germ_algebraMap_overSections K hz c).symm

end StalkAlgebra

/-! ## Principal ideals of a local Dedekind domain are maximal-ideal powers -/

/-- **A nonzero principal ideal of a local Dedekind domain (a DVR) is the count-th power of
the maximal ideal**: every prime factor of `(g)` is a nonzero prime, hence maximal, hence
*the* maximal ideal, so the factorization multiset is `count` copies of it. -/
theorem span_singleton_eq_maximalIdeal_pow_count {S : Type*} [CommRing S]
    [IsDedekindDomain S] [IsLocalRing S] {g : S} (hg : g ≠ 0) :
    Ideal.span {g} = maximalIdeal S
        ^ Multiset.count (maximalIdeal S) (factors (Ideal.span {g})) := by
  have hI : Ideal.span {g} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  have hall : ∀ P ∈ factors (Ideal.span {g}), P = maximalIdeal S := by
    intro P hP
    have hprime : Prime P := prime_of_factor _ hP
    haveI : P.IsPrime := Ideal.isPrime_of_prime hprime
    exact IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal ‹P.IsPrime› hprime.ne_zero)
  have hrepl : factors (Ideal.span {g})
      = Multiset.replicate (Multiset.card (factors (Ideal.span {g}))) (maximalIdeal S) :=
    Multiset.eq_replicate_card.mpr hall
  conv_lhs => rw [← associated_iff_eq.mp (factors_prod hI)]
  rw [hrepl, Multiset.prod_replicate, Multiset.count_replicate_self]

/-! ## The stalk colength dictionary -/

section StalkColength

attribute [local instance] Scheme.overSectionsAlgebra Scheme.stalkOverAlgebra
  Scheme.residueFieldOverModule

variable (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  {V : X.Opens} (hV : IsAffineOpen V) [IsDedekindDomain Γ(X, V)]

include hV in
/-- Shared master proof of finiteness and the finrank formula for the stalk quotient. -/
private theorem stalkQuot_master {z : X} (hz : z ∈ V) (hzg : z ≠ genericPoint X)
    {f : Γ(X, V)} (hf : f ≠ 0) :
    Module.Finite K (X.presheaf.stalk z ⧸ Ideal.span {(X.presheaf.germ V z hz).hom f})
      ∧ finrank K (X.presheaf.stalk z ⧸ Ideal.span {(X.presheaf.germ V z hz).hom f})
        = Multiset.count (hV.primeIdealOf ⟨z, hz⟩).asIdeal (factors (Ideal.span {f}))
            * X.residueDeg K z := by
  haveI : Nonempty V := ⟨⟨z, hz⟩⟩
  letI : Algebra Γ(X, V) (X.presheaf.stalk z) := X.presheaf.algebra_section_stalk ⟨z, hz⟩
  haveI hloc : IsLocalization.AtPrime (X.presheaf.stalk z)
      (hV.primeIdealOf ⟨z, hz⟩).asIdeal := hV.isLocalization_stalk ⟨z, hz⟩
  haveI : IsScalarTower K Γ(X, V) (X.presheaf.stalk z) :=
    Scheme.stalkOverAlgebra_isScalarTower K hz
  haveI : (hV.primeIdealOf ⟨z, hz⟩).asIdeal.IsMaximal :=
    hV.primeIdealOf_isMaximal_of_isClosed ⟨z, hz⟩
      (isClosed_singleton_of_ne_genericPoint (X ↘ Spec (CommRingCat.of K)) hzg)
  haveI := isDedekindDomain_stalk (X ↘ Spec (CommRingCat.of K)) hzg
  have hp0 : (hV.primeIdealOf ⟨z, hz⟩).asIdeal ≠ ⊥ := hV.primeIdealOf_ne_bot hz hzg
  haveI : Module.Finite K (Γ(X, V) ⧸ (hV.primeIdealOf ⟨z, hz⟩).asIdeal) :=
    moduleFinite_quotient_primeIdealOf K hV hz hzg
  have hgerm : (X.presheaf.germ V z hz).hom f
      = algebraMap Γ(X, V) (X.presheaf.stalk z) f := rfl
  have hfS : algebraMap Γ(X, V) (X.presheaf.stalk z) f ≠ 0 := fun h0 =>
    hf (germ_injective_of_isIntegral X z hz (by rw [hgerm, h0, map_zero]))
  set e := Multiset.count (hV.primeIdealOf ⟨z, hz⟩).asIdeal (factors (Ideal.span {f}))
    with he
  have hcount : Multiset.count (maximalIdeal (X.presheaf.stalk z))
      (factors (Ideal.span {algebraMap Γ(X, V) (X.presheaf.stalk z) f})) = e :=
    count_factors_span_algebraMap (X.presheaf.stalk z) hp0 hf
  have hspan : Ideal.span {(X.presheaf.germ V z hz).hom f}
      = maximalIdeal (X.presheaf.stalk z) ^ e := by
    rw [hgerm, span_singleton_eq_maximalIdeal_pow_count hfS, hcount]
  rw [hspan]
  haveI : Module.Finite K (Γ(X, V) ⧸ (hV.primeIdealOf ⟨z, hz⟩).asIdeal ^ e) :=
    moduleFinite_quotient_pow_atPrime (S := X.presheaf.stalk z) hp0 e
  refine ⟨Module.Finite.equiv
    (quotPowLinearEquiv (X.presheaf.stalk z) (hV.primeIdealOf ⟨z, hz⟩).asIdeal e), ?_⟩
  rw [← (quotPowLinearEquiv (X.presheaf.stalk z)
      (hV.primeIdealOf ⟨z, hz⟩).asIdeal e).finrank_eq,
    finrank_quotient_pow_atPrime (S := X.presheaf.stalk z) hp0 e,
    finrank_quotient_primeIdealOf K hV hz hzg]

include hV in
/-- **Finiteness of the stalk colength module**: the quotient of the DVR stalk at a closed
chart point by the germ of a nonzero chart section is a finite `K`-module. -/
theorem moduleFinite_stalkQuot_span_germ {z : X} (hz : z ∈ V) (hzg : z ≠ genericPoint X)
    {f : Γ(X, V)} (hf : f ≠ 0) :
    Module.Finite K (X.presheaf.stalk z ⧸ Ideal.span {(X.presheaf.germ V z hz).hom f}) :=
  (stalkQuot_master K hV hz hzg hf).1

include hV in
/-- **The stalk colength dictionary** (the pointwise face of SB-3b): for a closed point `z`
of the affine chart `V` of the curve bundle `X/K` and a nonzero chart section `f`, the
`K`-colength of the germ of `f` in the stalk is the multiplicity of the prime of `z` in the
factorization of `(f)`, weighted by the residue degree:

`finrank K (𝒪_{X,z} ⧸ (germ_z f)) = count p_z (factors (f)) · [κ(z) : K]`.

Transported to the chart along `quotPowLinearEquiv` (`B ⧸ p^e ≃ₗ[K] 𝒪_z ⧸ m^e`), where the
per-prime collapse (`finrank_quotient_pow_atPrime`) and the residue leg
(`finrank_quotient_primeIdealOf`) apply; the germ ideal is `m^e` by
`span_singleton_eq_maximalIdeal_pow_count` with the multiplicity preserved by localization
(`count_factors_span_algebraMap`). -/
theorem finrank_stalkQuot_span_germ {z : X} (hz : z ∈ V) (hzg : z ≠ genericPoint X)
    {f : Γ(X, V)} (hf : f ≠ 0) :
    finrank K (X.presheaf.stalk z ⧸ Ideal.span {(X.presheaf.germ V z hz).hom f})
      = Multiset.count (hV.primeIdealOf ⟨z, hz⟩).asIdeal (factors (Ideal.span {f}))
          * X.residueDeg K z :=
  (stalkQuot_master K hV hz hzg hf).2

end StalkColength

end AlgebraicGeometry
