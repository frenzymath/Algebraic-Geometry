/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Tangent.DualNumberTestObject
import AlgebraicJacobian.Picard.JacobianData

/-!
# The tangent space of the Jacobian at the identity (W5-T5, the scalar-identity spine)

The Wave-5 tangent statements phrased against the pinned representability datum
`(d : JacobianData C)` (roadmap `AJCR.w5-av.t5`), assembling the generic kit of
`Tangent/` into the two forms Wave 5 actually consumes:

```
Dual κ(e) (m_e/m_e²)  ≃  T_e(d.J)  ≃  ker (Pic⁰(Spec k[ε]) →* Pic⁰(Spec k))
```

and, under the **one** remaining numerical input, the frozen scalar identity
`dim_κ(e) m_e/m_e² = genus C` together with its additive consequence
`m_e/m_e² ≃+ H¹(C, 𝒪_C)`.

## The scalar-identity-first discipline (w5-worksheet D6), and what it buys

The W12 lesson recorded in the worksheet is that dimension transport must go
through **one** `finrank` identity, followed by **one** non-canonical `≃+` — not
through a chain of additive equivalences each carrying its own linearity
bookkeeping. This file is that discipline made structural:

* `JacobianData.tangentSpaceEquivPic0Kernel` is the representability leg,
  unconditional and sorry-free. It is a bijection of **sets**; it deliberately
  does *not* claim to transport dimension (a bare `Equiv` cannot).
* `JacobianData.finrank_cotangentSpaceDual_eq_genus` isolates the numerical
  content as a **hypothesis** `hdim`. That hypothesis is what the T3/T4 chain must
  deliver.
* `JacobianData.nonempty_cotangentSpace_addEquiv_h1` then produces the additive
  equivalence from the count, once.

So the Wave-5 tangent keystone is, at HEAD, reduced to a statement about the
`ε`-kernel of `pic0Functor` — **but note precisely which statement**. The
`ε`-kernel *bijection* above is not enough on its own: it is a bijection of sets,
and `finrank` does not transport along one. What `hdim` needs is the **semilinear
comparison** — an additive equivalence plus the intertwining law across
`κ(e) ≃+* k` — fed through `finrank_eq_of_addEquiv_of_bijective_smul` (proved
below, unconditionally). Stating T3/T4's target as a bare kernel bijection would
leave the count unreachable; this is the same residue the AJC sibling isolated as
`semilinearComparison_cotangentSpaceDual_h1Cok`. See inbox I-0513.

Note that the
identity point of `d.J` needs no rationality hypothesis: it is the image of the
group-object unit, hence a section, hence automatically `k`-rational
(`bijective_algebraMap_residueField_of_section`).

## Main declarations

* `AlgebraicGeometry.JacobianData.identitySection` — the `k`-rational identity
  point of `d.J`, with `identitySection_isSection`.
* `AlgebraicGeometry.JacobianData.tangentSpaceCotangentDual` — `T_0(d.J)` is the
  `κ(e)`-linear dual of the cotangent space at the identity.
* `AlgebraicGeometry.JacobianData.tangentSpaceEquivPic0Kernel` — `T_0(d.J)` is
  the `ε`-kernel of `pic0Functor C` (the representability leg, applied).
* `AlgebraicGeometry.JacobianData.cotangentSpaceDual_equiv_pic0Kernel` — the two
  composed: the cotangent dual at the identity *is* the `ε`-kernel.
* `AlgebraicGeometry.JacobianData.finiteDimensional_cotangentSpace` — the
  cotangent space at the identity is finite-dimensional (from
  `d.locallyOfFiniteType`).
* `AlgebraicGeometry.JacobianData.finrank_eq_of_addEquiv_of_bijective_smul` —
  **unconditional**: `finrank` transports across a scalar *bijection* given an
  additive equivalence and the intertwining law. The bridge that makes the count
  reachable at all.
* `AlgebraicGeometry.JacobianData.finrank_cotangentSpaceDual_eq_genus` /
  `nonempty_cotangentSpace_addEquiv_h1` — the frozen scalar identity and its
  additive consequence, each conditional on the T3/T4 semilinear comparison.

Reference: Kleiman, "The Picard scheme", §5 Thm. 5.11 (arXiv:math/0504020);
Milne, "Abelian varieties", Prop. 2.1.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u v

open CategoryTheory IsLocalRing Opposite

namespace AlgebraicGeometry

namespace JacobianData

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]

/-- **The identity point of the Jacobian.** The underlying scheme morphism
`Spec k ⟶ d.J.left` of the group-object unit — the `k`-rational point at which
Wave 5 computes the tangent space. -/
noncomputable def identitySection (d : JacobianData C) : Spec (.of k) ⟶ d.J.left :=
  letI := d.grpObj
  GroupScheme.identitySection d.J

/-- The identity point is a section of the structural morphism (the unit is a
morphism of `Over (Spec k)` out of the monoidal unit). -/
lemma identitySection_isSection (d : JacobianData C) :
    d.identitySection ≫ d.J.hom = 𝟙 (Spec (.of k)) :=
  letI := d.grpObj
  GroupScheme.identitySection_comp d.J

/-- **The tangent space of the Jacobian at the identity, as a cotangent dual**
(Kleiman §5 Thm. 5.11, LHS). The pointed dual-number points of `d.J` at the
identity form the `κ(e)`-linear dual of the cotangent space `m_e/m_e²`. No
rationality hypothesis is needed: the identity point is a section, hence
automatically `k`-rational. -/
noncomputable def tangentSpaceCotangentDual (d : JacobianData C) :
    pointedDualNumberPoints d.J d.identitySection ≃
      Module.Dual
        (ResidueField (d.J.left.presheaf.stalk (d.identitySection.base default)))
        (CotangentSpace (d.J.left.presheaf.stalk (d.identitySection.base default))) :=
  haveI : Subsingleton ↥(Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  overDualNumberSectionEquivCotangentSpaceDual d.J (d.identitySection_isSection)
    (congrArg _ (Subsingleton.elim _ _))

/-- **The representability leg, applied** (Kleiman §5 Thm. 5.11): the tangent
space of `d.J` at the identity is the **kernel** of the restriction
homomorphism

```
Pic⁰_{C/k}(Spec k[ε]) →* Pic⁰_{C/k}(Spec k)
```

along the `ε ↦ 0` point. Immediate from `pointedDualNumberPointsEquivKer` at the
pinned datum `d.rep`, whose functor is `pic0Functor C` composed with the
forgetful functors — note the `forget₂ ⋙ forget` typing of `rep` is exactly what
makes the group-valued kernel meaningful, and `JacobianData` owns that massage.

⚠ A bijection of **sets**: it does not transport `finrank`. That is the point of
the scalar-identity-first discipline — see the module docstring. -/
noncomputable def tangentSpaceEquivPic0Kernel (d : JacobianData C) :
    pointedDualNumberPoints d.J d.identitySection ≃
      {a : (pic0Functor C).obj (op (overDualNumber k)) //
        ((pic0Functor C).map (overDualNumberZero k).op).hom a = 1} :=
  pointedDualNumberPointsEquivKer d.J (pic0Functor C) d.rep d.identitySection_isSection

/-- **The two legs composed**: the `κ(e)`-linear dual of the cotangent space at
the identity of `d.J` *is* the `ε`-kernel of `Pic⁰_{C/k}`. This is the statement
the T3/T4 chain computes against, and the one whose dimension T5 counts. -/
noncomputable def cotangentSpaceDual_equiv_pic0Kernel (d : JacobianData C) :
    Module.Dual
        (ResidueField (d.J.left.presheaf.stalk (d.identitySection.base default)))
        (CotangentSpace (d.J.left.presheaf.stalk (d.identitySection.base default)))
      ≃ {a : (pic0Functor C).obj (op (overDualNumber k)) //
          ((pic0Functor C).map (overDualNumberZero k).op).hom a = 1} :=
  d.tangentSpaceCotangentDual.symm.trans d.tangentSpaceEquivPic0Kernel

/-- **Finite-dimensionality of the cotangent space at the identity.** The
Jacobian is locally of finite type over `k` by the datum's certificate, hence
locally Noetherian, so `m_e/m_e²` is a finite-dimensional `κ(e)`-vector space —
the input any dimension count needs. -/
theorem finiteDimensional_cotangentSpace (d : JacobianData C) :
    FiniteDimensional
      (ResidueField (d.J.left.presheaf.stalk (d.identitySection.base default)))
      (CotangentSpace (d.J.left.presheaf.stalk (d.identitySection.base default))) :=
  letI := d.locallyOfFiniteType
  letI : IsLocallyNoetherian d.J.left := LocallyOfFiniteType.isLocallyNoetherian d.J.hom
  inferInstance

/-! ## The frozen scalar identity, and the bridge T3/T4 must actually cross

Everything above is unconditional. What follows carries the numerical input as an
explicit hypothesis, named once:

```
hdim : Module.finrank κ(e) (m_e/m_e²) = genus C
```

Keeping it a hypothesis rather than a `sorry` is the w5-worksheet §0(4) rule
(never register a staged fact).

**What `hdim` needs, stated precisely — the `ε`-kernel bijection alone is NOT
enough.** `tangentSpaceEquivPic0Kernel` is a bijection of *sets* (it says so on
its own docstring) and a bare `Equiv` does not determine `finrank`. So T3/T4's
kernel computation does not by itself give `hdim`: additionally required is an
**additive** equivalence together with the intertwining law across the
residue-field bijection `κ(e) → k`, because the two sides are modules over
genuinely different rings — neither `LinearEquiv.finrank_eq` nor a
`restrictScalars` argument applies.

`finrank_eq_of_addEquiv_of_bijective_smul` below is exactly that bridge, and it
is unconditional. With it in hand the residual obligation on T3/T4 is the
**semilinear comparison**: a scalar bijection `i`, an additive equivalence `j`
from `Dual κ(e) (m_e/m_e²)` to `H¹(C,𝒪)`, and `j (r • x) = i r • j x`. That is
the honest target to state T3/T4 against — and it is the same residue the AJC
sibling isolated (`semilinearComparison_cotangentSpaceDual_h1Cok`), which is why
porting the generic kit without this bridge would have left the count
unreachable. Found by fresh-context review; see inbox I-0513. -/

/-- **`finrank` across a scalar bijection** (the linearity bridge the Wave-5
count needs, and the reason the `ε`-kernel *set* bijection is insufficient on its
own). If `i : R → R'` is a bijection of scalars, `j : M ≃+ M₁` an additive
equivalence, and the two intertwine (`j (r • m) = i r • j m`), then `M` and `M₁`
have equal `finrank` over their respective rings.

`i` need only be a **bijection**, not a ring homomorphism, and the module
structures live over genuinely different rings — which is precisely the situation
of the Kleiman §5 Thm. 5.11 count, comparing a `κ(e)`-dimension with a
`k`-dimension across `κ(e) ≃+* k`. Mathlib has this at the level of
`Module.rank` (`rank_eq_of_equiv_equiv`) but not in `finrank` form; this is the
`Module.finrank = toNat ∘ Module.rank` unfolding of it. -/
theorem finrank_eq_of_addEquiv_of_bijective_smul
    {R : Type*} {R' : Type*} {M M₁ : Type v} [Semiring R] [AddCommMonoid M] [Module R M]
    [Semiring R'] [AddCommMonoid M₁] [Module R' M₁]
    (i : R → R') (j : M ≃+ M₁) (hi : Function.Bijective i)
    (hc : ∀ (r : R) (m : M), j (r • m) = i r • j m) :
    Module.finrank R M = Module.finrank R' M₁ := by
  unfold Module.finrank
  rw [rank_eq_of_equiv_equiv i j hi hc]

variable (d : JacobianData C)

/-- **The frozen scalar identity** `dim_κ(e) T₀(d.J) = genus C`, conditional on
the T3/T4 count. Stated in cotangent form: since `T₀(d.J)` is by
`tangentSpaceCotangentDual` the `κ(e)`-linear dual of `m_e/m_e²` and the latter
is finite-dimensional (`finiteDimensional_cotangentSpace`), the dual has the same
dimension, so this single `finrank` equation *is* the Wave-5 dimension
statement — no further transport is needed or wanted (w5-worksheet D6).

The hypothesis is exactly what T3/T4 produce; nothing else in Wave 5 needs the
`ε`-kernel in any other form. -/
theorem finrank_cotangentSpaceDual_eq_genus
    (hdim : Module.finrank
        (ResidueField (d.J.left.presheaf.stalk (d.identitySection.base default)))
        (CotangentSpace (d.J.left.presheaf.stalk (d.identitySection.base default)))
      = genus C) :
    Module.finrank
        (ResidueField (d.J.left.presheaf.stalk (d.identitySection.base default)))
        (Module.Dual
          (ResidueField (d.J.left.presheaf.stalk (d.identitySection.base default)))
          (CotangentSpace
            (d.J.left.presheaf.stalk (d.identitySection.base default))))
      = genus C := by
  rw [Subspace.dual_finrank_eq]
  exact hdim

/-- **The Wave-5 tangent keystone, additively** (Kleiman §5 Thm. 5.11): the
cotangent space at the identity of `d.J` is additively isomorphic to
`H¹(C, 𝒪_C)`, given the scalar identity. This is the "one non-canonical `≃+`
after one `finrank` identity" of the D6 discipline: the equivalence is produced
*once*, by choosing bases on both sides and transporting along `κ(e) ≃+* k`
(`nonempty_cotangentSpaceAddEquiv_of_finrank_eq`), and it is `Nonempty` because
that choice is not canonical.

`genus C` is by definition `finrank k H¹(C, 𝒪_C)` (`Challenge.lean`), so the
hypothesis really is the dimension comparison of the two sides. -/
theorem nonempty_cotangentSpace_addEquiv_h1
    [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
    (hdim : Module.finrank
        (ResidueField (d.J.left.presheaf.stalk (d.identitySection.base default)))
        (CotangentSpace (d.J.left.presheaf.stalk (d.identitySection.base default)))
      = genus C) :
    Nonempty
      (CotangentSpace (d.J.left.presheaf.stalk (d.identitySection.base default))
        ≃+ Sheaf.HModule (C.left.moduleKSheaf k) 1) :=
  letI := d.locallyOfFiniteType
  nonempty_cotangentSpaceAddEquiv_of_finrank_eq d.J d.identitySection_isSection
    (Sheaf.HModule (C.left.moduleKSheaf k) 1) hdim

end JacobianData

end AlgebraicGeometry
