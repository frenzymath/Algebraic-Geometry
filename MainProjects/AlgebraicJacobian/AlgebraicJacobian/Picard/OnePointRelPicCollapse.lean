/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.RelPicFunctor
import AlgebraicJacobian.Picard.Pic0DualNumberCocycle

/-!
# The relative Picard group at a one-point test object (A.3.iii, tangent lane)

At a test object `T` whose underlying space is a **single point** — for the tangent-space
computation the two cases are the dual numbers `Spec k[ε]` and the base `Spec k` itself —
the coset subgroup `π_T^* Pic(T)` that the *relative* Picard functor quotients out is
**trivial**, so

```
Pic(C ×_k T) / π_T^* Pic(T)  ≃+  Pic(C ×_k T).
```

The coset calculus of `PicSharp.relPresheaf` therefore disappears from the ε-kernel
computation entirely, and the dual-number kernel of the *relative* functor may be computed
on the *absolute* Picard group, where the two-chart Čech model of
`Picard/Pic0DualNumberCocycle.lean` §6 lives.

## Why this is cheap

`IsLocallyTrivial` asks for an affine open `U ∋ x` trivialising the module. On a one-point
space *every* nonempty open is `⊤`, so a locally trivial module is **globally** trivial and
no cover-splitting argument is needed. That is the whole content: the collapse is
**topological**, not commutative algebra about `Pic` of an Artin local ring.

The general-coefficient statement ("`Pic` of a finite product of Artin local rings
vanishes") is true, is genuine commutative algebra, and is *not needed here*.

## Main declarations

* `LineBundle.IsLocallyTrivial.trivial_of_subsingleton` — a locally trivial module on a
  one-point scheme is trivial. Scheme-general, no hypothesis on the module beyond local
  triviality.
* `PicSharp.relPicRel_iff_iso_of_subsingleton` — at a one-point test object the `H_T`-coset
  relation *is* the absolute iso-class relation, in both directions.
* `PicSharp.relPicQuotAddEquivAbs` — the resulting additive equivalence
  `Pic(C ×_S T)/π_T^* Pic(T) ≃+ Pic(C ×_S T)`, with the computation rule
  `PicSharp.relPicQuotAddEquivAbs_mk`.

Cross-project note: the sibling `Algebraic-Jacobian-Challenge-Rebuild` has the same collapse
on its own carrier (`Tangent/RelPicPointTest.lean`, `picFromBase_eq_bot_of_subsingleton`),
where the relative group is a `QuotientGroup` by an honest subgroup and the argument is five
lines on top of `CechPic.subsingleton_of_subsingleton`. This project's carrier is a *setoid*
quotient of `LineBundle.OnProduct` with no subgroup to name, so the collapse has to be proved
at the level of the relation — which is what the second declaration above does. The two are
the same mathematics on different carriers (inbox I-0495, 2026-07-28).

Reference: Kleiman, "The Picard scheme", §2 `df:Pfs`, §5 Thm. 5.11 (arXiv:math/0504020).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme

/-! ## §1. One-point spaces: local triviality is global triviality -/

/-- On a scheme with a subsingleton underlying space, an open containing a point is `⊤`.
The one topological input of this file. -/
theorem Opens.eq_top_of_subsingleton {T : Scheme.{u}} [Subsingleton T]
    (U : T.Opens) {x : T} (hx : x ∈ U) : U = ⊤ := by
  ext y
  refine iff_of_true ?_ trivial
  exact Subsingleton.elim y x ▸ hx

/-- Restriction to `⊤` undone: pulling back along `T.topIso.inv` inverts
`Modules.pullback (⊤ : T.Opens).ι`, since the composite of the two morphisms is `𝟙 T`
(`Scheme.toIso_inv_ι`). -/
noncomputable def Modules.pullbackTopIsoSelf {T : Scheme.{u}} (N : T.Modules) :
    (Scheme.Modules.pullback (T.topIso).inv).obj
        ((Scheme.Modules.pullback (⊤ : T.Opens).ι).obj N) ≅ N :=
  (Scheme.Modules.pullbackComp (T.topIso).inv (⊤ : T.Opens).ι).app N ≪≫
    (Scheme.Modules.pullbackCongr (T.toIso_inv_ι)).app N ≪≫
    (Scheme.Modules.pullbackId T).app N

/-- **A locally trivial module on a one-point scheme is globally trivial.**

Local triviality supplies an affine open `U ∋ x` with `N|_U ≅ 𝒪_U`; on a subsingleton space
`U = ⊤` (`Opens.eq_top_of_subsingleton`), and restriction to `⊤` is invertible
(`Modules.pullbackTopIsoSelf`), so the chart trivialisation *is* a global one.

Scheme-general and cover-free: no affine-cover gluing and no commutative algebra. -/
theorem LineBundle.IsLocallyTrivial.trivial_of_subsingleton {T : Scheme.{u}}
    [Subsingleton T] [Nonempty T] {N : T.Modules} (hN : LineBundle.IsLocallyTrivial N) :
    Nonempty (N ≅ SheafOfModules.unit T.ringCatSheaf) := by
  obtain ⟨U, hxU, _, ⟨e⟩⟩ := hN (Classical.arbitrary T)
  have hU : U = ⊤ := Opens.eq_top_of_subsingleton U hxU
  subst hU
  refine ⟨(Modules.pullbackTopIsoSelf N).symm ≪≫ ?_⟩
  refine (Scheme.Modules.pullback (T.topIso).inv).mapIso
    ((Scheme.Modules.restrictFunctorIsoPullback (⊤ : T.Opens).ι).symm.app N ≪≫ e) ≪≫ ?_
  exact Scheme.Modules.pullbackUnitIso _

namespace PicSharp

/-! ## §2. The coset relation collapses -/

/-- **The `H_T`-coset relation is the iso-class relation at a one-point test object.**

The nontrivial direction: a coset witness `N` on `T` is trivial by
`LineBundle.IsLocallyTrivial.trivial_of_subsingleton`, so `π_T^* N ≅ 𝒪_{C ×_S T}` and the
tensor factor cancels by the left unitor. The converse is `relPicRel_of_iso`, which holds
at any test object.

This is the statement that removes the relative quotient from the tangent-space computation:
`Pic^♯_{C/k}(Spec k[ε])` may be computed as the *absolute* `Pic(C_ε)`. -/
theorem relPicRel_iff_iso_of_subsingleton {S C T : Scheme.{u}} (πC : C ⟶ S) (πT : T ⟶ S)
    [Subsingleton T] [Nonempty T] {L L' : LineBundle.OnProduct πC πT} :
    relPicRel πC πT L L' ↔ Nonempty (L.carrier ≅ L'.carrier) := by
  refine ⟨fun h => ?_, relPicRel_of_iso⟩
  obtain ⟨N, hN, ⟨e⟩⟩ := h
  obtain ⟨eN⟩ := hN.trivial_of_subsingleton
  refine ⟨e ≪≫ ?_⟩
  refine Modules.tensorObjIsoOfIso ?_ (Iso.refl L'.carrier) ≪≫
    Modules.tensorObj_left_unitor L'.carrier
  exact (Scheme.Modules.pullback (Limits.pullback.snd πC πT)).mapIso eN ≪≫
    Scheme.Modules.pullbackUnitIso _

/-- The relative and absolute carrier setoids have the same relation at a one-point test
object (`relPicRel_iff_iso_of_subsingleton`, as an equality of relations). -/
theorem relPicSetoid_r_eq_of_subsingleton {S C T : Scheme.{u}} (πC : C ⟶ S) (πT : T ⟶ S)
    [Subsingleton T] [Nonempty T] :
    (relPicSetoid πC πT).r = (RelPicPresheaf.preimage_subgroup πC πT).r := by
  funext L L'
  exact propext (relPicRel_iff_iso_of_subsingleton πC πT)

/-! ## §3. The resulting identification of groups -/

/-- **`Pic(C ×_S T)/π_T^* Pic(T) ≃ Pic(C ×_S T)` at a one-point test object** — the
underlying equivalence of the collapse, the identity on representatives. -/
noncomputable def relPicQuotEquivAbs {S C T : Scheme.{u}} (πC : C ⟶ S) (πT : T ⟶ S)
    [Subsingleton T] [Nonempty T] :
    Quotient (relPicSetoid πC πT) ≃ Quotient (RelPicPresheaf.preimage_subgroup πC πT) :=
  Quotient.congr (Equiv.refl _) (fun a b => by
    rw [show (relPicSetoid πC πT).r a b ↔ _ from
      Iff.of_eq (congrFun (congrFun (relPicSetoid_r_eq_of_subsingleton πC πT) a) b)]
    rfl)

/-- **The collapse, additively**: the relative Picard group at a one-point test object *is*
the absolute Picard group as an additive group.

Additivity is `rfl` on representatives because both group structures are the descent of the
same tensor product (`addCommGroup_via_tensorObj` on the coset quotient,
`addCommGroup` on the iso-class quotient), and the equivalence is the identity on
representatives.

Additivity is the point: a bare `Equiv` would not transport `finrank`, which is what the
tangent-space dimension count needs (inbox I-0495, 2026-07-28). -/
noncomputable def relPicQuotAddEquivAbs {S C T : Scheme.{u}} (πC : C ⟶ S) (πT : T ⟶ S)
    [Subsingleton T] [Nonempty T] :
    Quotient (relPicSetoid πC πT) ≃+ Quotient (RelPicPresheaf.preimage_subgroup πC πT) where
  __ := relPicQuotEquivAbs πC πT
  map_add' a b := by
    induction a using Quotient.ind with | _ L => ?_
    induction b using Quotient.ind with | _ L' => ?_
    rfl

@[simp]
theorem relPicQuotAddEquivAbs_mk {S C T : Scheme.{u}} (πC : C ⟶ S) (πT : T ⟶ S)
    [Subsingleton T] [Nonempty T] (L : LineBundle.OnProduct πC πT) :
    relPicQuotAddEquivAbs πC πT (Quotient.mk _ L) = Quotient.mk _ L := rfl

/-- **The collapse at the functor-object carriers** — the spelling every consumer of
`PicSharp.relPresheaf` actually sees.

Mathematically identical to `relPicQuotAddEquivAbs`, but stated against
`(relPresheaf C).obj (op T)` and `(PicSharp C).obj (op T)` rather than the bare `Quotient`s.
That is not cosmetic: the two agree only up to `AddCommGrpCat.of`, and at `instances`
transparency Lean will *not* accept one where the other is expected — `AddMonoidHom.mem_ker`
against the raw `Quotient` fails with a `Membership` instance mismatch. Restating here once
means no consumer has to fight it. -/
noncomputable def relPresheafObjAddEquivAbs {k : Type u} [Field k]
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    (T : Over (Spec (CommRingCat.of k))) [Subsingleton T.left] [Nonempty T.left] :
    (PicSharp.relPresheaf C).obj (Opposite.op T) ≃+ (PicSharp C).obj (Opposite.op T) :=
  relPicQuotAddEquivAbs C.hom T.hom

/-! ## §4. The dual-number specialisation: the ε-kernel leaves the relative world

The tangent lane needs the collapse at exactly two test objects, and both are one-point
spaces: `Spec k[ε]` (a local ring with nilpotent maximal ideal) and `Spec k`. The four
instances below are what make the collapse *apply* there, and the two theorems transport the
dual-number kernel — the functor-of-points tangent space of `Pic^♯_{C/k}` at the identity —
from the relative functor onto the absolute Picard group, where the two-chart Čech
unit-cocycle model of `Picard/Pic0DualNumberCocycle.lean` §6 lives. -/

instance subsingleton_overDualNumber_left (k : Type u) [Field k] :
    Subsingleton (overDualNumber k).left :=
  inferInstanceAs (Subsingleton (PrimeSpectrum (DualNumber k)))

instance nonempty_overDualNumber_left (k : Type u) [Field k] :
    Nonempty (overDualNumber k).left :=
  inferInstanceAs (Nonempty (PrimeSpectrum (DualNumber k)))

instance subsingleton_overTrivial_left (k : Type u) [Field k] :
    Subsingleton (Over.mk (𝟙 (Spec (CommRingCat.of k)))).left :=
  inferInstanceAs (Subsingleton (PrimeSpectrum k))

instance nonempty_overTrivial_left (k : Type u) [Field k] :
    Nonempty (Over.mk (𝟙 (Spec (CommRingCat.of k)))).left :=
  inferInstanceAs (Nonempty (PrimeSpectrum k))

/-- **The collapse intertwines the two `ε ↦ 0` restriction homomorphisms.** Naturality of the
collapse at the one morphism the tangent lane restricts along; `rfl` on representatives,
because both functorial actions are the same pullback descended through different
quotients. -/
theorem relPresheafObjAddEquivAbs_map_overDualNumberZero {k : Type u} [Field k]
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    (a : (PicSharp.relPresheaf C).obj (Opposite.op (overDualNumber k))) :
    relPresheafObjAddEquivAbs C (Over.mk (𝟙 (Spec (CommRingCat.of k))))
        (((PicSharp.relPresheaf C).map (overDualNumberZero k).op).hom a)
      = ((PicSharp C).map (overDualNumberZero k).op).hom
          (relPresheafObjAddEquivAbs C (overDualNumber k) a) := by
  induction a using Quotient.ind with | _ L => ?_
  rfl

/-- Membership in the relative ε-kernel is membership in the absolute ε-kernel, transported.
Both directions, the reverse one by injectivity of the collapse at `Spec k`. -/
theorem mem_ker_relPresheaf_iff {k : Type u} [Field k]
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    (a : (PicSharp.relPresheaf C).obj (Opposite.op (overDualNumber k))) :
    a ∈ ((PicSharp.relPresheaf C).map (overDualNumberZero k).op).hom.ker ↔
      relPresheafObjAddEquivAbs C (overDualNumber k) a ∈
        ((PicSharp C).map (overDualNumberZero k).op).hom.ker := by
  simp only [AddMonoidHom.mem_ker,
    ← relPresheafObjAddEquivAbs_map_overDualNumberZero C a]
  exact ⟨fun h => by rw [h]; exact map_zero _,
    fun h => (relPresheafObjAddEquivAbs C
      (Over.mk (𝟙 (Spec (CommRingCat.of k))))).injective (h.trans (map_zero _).symm)⟩

/-- **The dual-number kernel of the RELATIVE Picard functor is the dual-number kernel of the
ABSOLUTE Picard group** — additively.

This is what the collapse buys the tangent lane. `relPicDualKernel C`
(`Picard/Pic0AbelianVariety.lean`) is the left-hand side; the right-hand side is a kernel on
`Pic(C ×_k Spec k[ε])`, which is where the two-chart Čech unit-cocycle engine computes. So
the cocycle comparison no longer has to see the `H_T`-coset quotient at all.

Additive, not a bare `Equiv`: the tangent-space dimension count transports `finrank`. -/
noncomputable def kerRelPresheafAddEquivKerAbs {k : Type u} [Field k]
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] :
    ((PicSharp.relPresheaf C).map (overDualNumberZero k).op).hom.ker ≃+
      ((PicSharp C).map (overDualNumberZero k).op).hom.ker where
  toFun a := ⟨relPresheafObjAddEquivAbs C (overDualNumber k) a.1,
    (mem_ker_relPresheaf_iff C a.1).mp a.2⟩
  invFun b := ⟨(relPresheafObjAddEquivAbs C (overDualNumber k)).symm b.1,
    (mem_ker_relPresheaf_iff C _).mpr (by rw [AddEquiv.apply_symm_apply]; exact b.2)⟩
  left_inv a := Subtype.ext (AddEquiv.symm_apply_apply _ _)
  right_inv b := Subtype.ext (AddEquiv.apply_symm_apply _ _)
  map_add' a b := Subtype.ext (map_add _ _ _)

end PicSharp

end Scheme

end AlgebraicGeometry
