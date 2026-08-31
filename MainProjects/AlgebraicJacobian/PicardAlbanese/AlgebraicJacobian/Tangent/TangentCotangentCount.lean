/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.AlgebraicGeometry.Noetherian
import AlgebraicJacobian.Tangent.TangentIdentitySection

/-!
# Tangent-space endgame substrate: the cotangent space vs `H¹` by dimension count

The **scalar-identity-first** reduction of the Kleiman §5 Thm.~5.11 tangent
keystone (w5-worksheet D6; the W12 lesson: ONE `finrank` identity, then one
non-canonical `≃+`). The Wave-5 target asks for an **additive** equivalence
between the cotangent space `m_e/m_e²` at the (`k`-rational) identity-section
point of the Jacobian and the cohomology `k`-module `H¹(C, 𝒪_C)`,
non-canonically (`Nonempty`). Such an equivalence is pure linear algebra once
the two sides are

1. finite-dimensional vector spaces — over `κ(e)` (local Noetherianity of a
   scheme locally of finite type over a field) resp. over `k` (the genus-lane
   finiteness of `Sheaf.HModule (C.left.moduleKSheaf k) 1`), with
2. `κ(e) ≃+* k` (the image of a section of the structure morphism is a
   `k`-rational point, `bijective_algebraMap_residueField_of_section`), and
3. equal dimensions.

This file provides that reduction as reusable infrastructure:

- `Module.nonempty_addEquiv_of_finrank_eq_of_ringEquiv` — finite-dimensional
  vector spaces over fields identified by a ring isomorphism are additively
  equivalent iff-wise as soon as their dimensions agree (choose bases).
- `AlgebraicGeometry.nonempty_cotangentSpaceAddEquiv_of_finrank_eq` — the
  scheme-level form: for `X` locally of finite type over `Spec k`, a section
  `e` of the structure morphism, and a finite `k`-module `W`, an equality
  `dim_{κ(e)} m_e/m_e² = dim_k W` yields `m_e/m_e² ≃+ W`.

Consequently the whole content of the Wave-5 tangent keystone (Kleiman FGA
Explained 5.11: `T₀ J ≅ H¹(C, 𝒪_C)`) is reduced to the **dimension identity**
`dim_{κ(e)} m_e/m_e² = dim_k H¹(C, 𝒪_C)` at `e` the identity section. That
identity is what T3/T4 supply: the representability leg (the `ε`-kernel
description of the dual-number points, `Tangent/Pic0TangentSpace.lean`) and the
truncated-exponential Čech leg (`Tangent/TruncExpCech*.lean`, brick T2, landed).

## Provenance (W5-T1 port, cross-project)

Ported from `Algebraic-Jacobian-Challenge`,
`AlgebraicJacobian/Picard/Pic0TangentSpace.lean` (sorry-free, mathlib
generality; renamed here because the Rebuild reserves `Pic0TangentSpace.lean`
for the datum-phrased consumers). See `Tangent/TangentDualNumbers.lean` and
inbox `I-0495`. Import list trimmed to what the declarations use.

Source: Kleiman, "The Picard scheme", §5 Thm.~5.11 (arXiv:math/0504020).
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u v w w'

open CategoryTheory IsLocalRing

/-- **Equal-dimension finite-dimensional vector spaces over isomorphic fields
are additively equivalent.** For fields `K ≃+* L`, a finite-dimensional
`K`-vector space `V` and a finite-dimensional `L`-vector space `W` with
`dim_K V = dim_L W` admit an additive equivalence `V ≃+ W`: choose finite
bases on both sides (`Module.finBasis`) and transport the coordinates along
the field isomorphism componentwise. Non-canonical (basis choice), hence the
`Nonempty`. -/
theorem Module.nonempty_addEquiv_of_finrank_eq_of_ringEquiv
    {K : Type u} {L : Type v} [Field K] [Field L]
    {V : Type w} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {W : Type w'} [AddCommGroup W] [Module L W] [FiniteDimensional L W]
    (e : K ≃+* L) (h : Module.finrank K V = Module.finrank L W) :
    Nonempty (V ≃+ W) :=
  ⟨((Module.finBasis K V).equivFun.toAddEquiv.trans
      (AddEquiv.piCongrRight fun _ => e.toAddEquiv)).trans
    ((Module.finBasis L W).reindex (finCongr h.symm)).equivFun.toAddEquiv.symm⟩

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- **The cotangent space at a section, additively, by dimension count.** Let
`X` be a scheme locally of finite type over `Spec k` and `e` a section of the
structure morphism, so that `x = e(*)` is a `k`-rational point and the
cotangent space `m_x/m_x²` is a finite-dimensional `κ(x)`-vector space. For
any finite `k`-module `W` of the same dimension there is an additive
equivalence `m_x/m_x² ≃+ W` (non-canonical: transport bases along
`κ(x) ≃+* k`).

This is the generic linear-algebra half of Kleiman §5 Thm.~5.11 for
`X = d.J`, `W = H¹(C, 𝒪_C)`: it reduces the Wave-5 tangent keystone to the
dimension identity `dim_{κ(e)} m_e/m_e² = dim_k H¹(C, 𝒪_C)` (= `genus C`, by
the definition of `genus` in `Challenge.lean`). -/
theorem nonempty_cotangentSpaceAddEquiv_of_finrank_eq
    (X : Over (Spec (CommRingCat.of k))) [LocallyOfFiniteType X.hom]
    {e : Spec (CommRingCat.of k) ⟶ X.left}
    (he : e ≫ X.hom = 𝟙 (Spec (CommRingCat.of k)))
    (W : Type w) [AddCommGroup W] [Module k W] [Module.Finite k W]
    (h : Module.finrank
          (ResidueField (X.left.presheaf.stalk (e.base default)))
          (CotangentSpace (X.left.presheaf.stalk (e.base default)))
        = Module.finrank k W) :
    Nonempty
      (CotangentSpace (X.left.presheaf.stalk (e.base default)) ≃+ W) := by
  haveI : Subsingleton ↥(Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  -- `e(*)` is a `k`-rational point: `k ≃+* κ(e(*))`.
  have hres : Function.Bijective
      (algebraMap k (ResidueField (X.left.presheaf.stalk (e.base default)))) :=
    bijective_algebraMap_residueField_of_section X he
      (congrArg _ (Subsingleton.elim _ _))
  -- the cotangent space is finite-dimensional over the residue field
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  haveI : FiniteDimensional
      (ResidueField (X.left.presheaf.stalk (e.base default)))
      (CotangentSpace (X.left.presheaf.stalk (e.base default))) :=
    inferInstance
  exact Module.nonempty_addEquiv_of_finrank_eq_of_ringEquiv
    (residueFieldEquivOfBijective hres).symm h

/-! ## Pointed dual-number points along an open immersion

A clopen-transport connector for the Kleiman §5 Thm.~5.11 dimension identity:
the Zariski tangent space of an open subgroup scheme at a point is the tangent
space of the ambient scheme there, because `Spec k[ε]` is a one-point scheme,
so a pointed dual-number point of the ambient scheme at a point of an open
subscheme factors (uniquely) through the open immersion. Stated for an
arbitrary morphism of `Over (Spec k)`-schemes whose underlying morphism is an
open immersion.

The Rebuild's `pic0Functor` is degree-zero *by definition* (a subgroup of
`picEt`, not an identity component carved out of a larger Picard scheme), so
this connector is **not** on the Rebuild's critical path the way it is on the
sibling's — it is kept because it is generic, cheap, and the natural tool if a
later lane does introduce an open immersion `d.J ↪ (something bigger)`. -/

/-- The spectrum of the dual numbers over a field is a one-point space: every
prime of `k[ε]` is the maximal ideal, since every nonunit `x` has vanishing
constant component, hence `x² = 0` lies in every prime. -/
instance DualNumber.instSubsingletonPrimeSpectrum :
    Subsingleton (PrimeSpectrum (DualNumber k)) := by
  constructor
  have key : ∀ p : PrimeSpectrum (DualNumber k),
      p.asIdeal = maximalIdeal (DualNumber k) := by
    intro p
    refine le_antisymm (le_maximalIdeal p.isPrime.ne_top) fun x hx => ?_
    have hfst : TrivSqZeroExt.fst x = 0 := by
      by_contra h0
      exact hx (TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (isUnit_iff_ne_zero.mpr h0))
    have hsq : x * x = 0 := by
      have hxr : x = TrivSqZeroExt.inr (TrivSqZeroExt.snd x) := by
        conv_lhs => rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq x]
        rw [hfst, TrivSqZeroExt.inl_zero, zero_add]
      rw [hxr, TrivSqZeroExt.inr_mul_inr]
    exact p.isPrime.mem_of_pow_mem 2 (by rw [pow_two, hsq]; exact p.asIdeal.zero_mem)
  intro p q
  exact PrimeSpectrum.ext ((key p).trans (key q).symm)

/-- **Pointed dual-number points transport along open immersions.** For a
morphism `f : X ⟶ Y` of schemes over `Spec k` whose underlying scheme
morphism is an open immersion, and a `k`-point `e` of `X`, composition with
`f` identifies the pointed dual-number points of `X` at `e(*)` with those of
`Y` at `f(e(*))`: since `Spec k[ε]` is a one-point scheme, any dual-number
point of `Y` landing at `f(e(*))` has range inside the open image of `f`,
hence lifts uniquely (`IsOpenImmersion.lift`). -/
noncomputable def pointedDualNumberPointsEquivOfOpenImmersion
    {X Y : Over (Spec (CommRingCat.of k))} (f : X ⟶ Y) [IsOpenImmersion f.left]
    (e : Spec (CommRingCat.of k) ⟶ X.left) :
    {g : Spec (CommRingCat.of (DualNumber k)) ⟶ X.left //
        g ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))
          ∧ g.base (closedPoint (DualNumber k)) = e.base default}
      ≃ {g : Spec (CommRingCat.of (DualNumber k)) ⟶ Y.left //
        g ≫ Y.hom = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))
          ∧ g.base (closedPoint (DualNumber k)) = (e ≫ f.left).base default} where
  toFun g :=
    ⟨g.1 ≫ f.left,
      by rw [Category.assoc, Over.w f]; exact g.2.1,
      by rw [Scheme.Hom.comp_apply, g.2.2, Scheme.Hom.comp_apply]⟩
  invFun h :=
    have hrange : Set.range h.1.base ⊆ Set.range f.left.base := by
      rintro - ⟨t, rfl⟩
      refine ⟨e.base default, ?_⟩
      have ht : t = closedPoint (DualNumber k) :=
        Subsingleton.elim (α := PrimeSpectrum (DualNumber k)) t _
      rw [ht, h.2.2, Scheme.Hom.comp_apply]
    ⟨IsOpenImmersion.lift f.left h.1 hrange,
      by rw [← Over.w f, ← Category.assoc, IsOpenImmersion.lift_fac]; exact h.2.1,
      by
        apply (Scheme.Hom.isOpenEmbedding f.left).injective
        rw [← Scheme.Hom.comp_apply, IsOpenImmersion.lift_fac, h.2.2,
          Scheme.Hom.comp_apply]⟩
  left_inv g :=
    Subtype.ext (by rw [← cancel_mono f.left]; exact IsOpenImmersion.lift_fac _ _ _)
  right_inv h := Subtype.ext (IsOpenImmersion.lift_fac _ _ _)

end AlgebraicGeometry
