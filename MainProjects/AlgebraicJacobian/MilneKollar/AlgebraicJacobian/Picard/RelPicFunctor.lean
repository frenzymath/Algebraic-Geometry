/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.Order.CompletePartialOrder
import AlgebraicJacobian.Picard.LineBundlePullback
import AlgebraicJacobian.Picard.TensorObjSubstrate
-- (v4.31.0: `exists_tensorObj_inverse` was moved from `TensorObjSubstrate` to `TensorObjInverse`
-- during the migration cleanup; import it here so this file resolves the public constant.)
import AlgebraicJacobian.Picard.TensorObjInverse
-- (the loc-triv pullback–tensor comparison iso `Modules.pullbackTensorIsoOfLocallyTrivial`,
-- i.e. the multiplicativity of `π_T^*`, used to build the relative Picard `H_T`-coset setoid
-- `relPicSetoid` below.)
import AlgebraicJacobian.Picard.TensorObjSubstrate.PullbackTensorIso

/-!
# The relative Picard functor and its étale sheafification

For a smooth proper geometrically integral curve `C` over a field `k`, this file upgrades
the set-valued relative Picard presheaf
`Pic^♯_{C/k}(T) := Pic(C ×_k T) / π_T^* Pic(T)` of
`AlgebraicJacobian/Picard/LineBundlePullback.lean` to an abelian-group-valued functor, and
then sheafifies it.  It feeds the positive-genus arm of `nonempty_jacobianWitness`.

## Main definitions

* `PicSharp.addCommGroup` — the abelian-group structure on
  `Quotient (RelPicPresheaf.preimage_subgroup πC πT)`: addition is the descent of the
  tensor product, `[L] + [L'] := [L ⊗ L']`, the zero is the class of the structure sheaf,
  and `-[L]` is the class of the tensor inverse of `L`.
* `relPicRel`, `relPicSetoid`, `PicSharp.addCommGroup_via_tensorObj` — the coarser
  `H_T`-coset relation, the setoid it defines, and the abelian group on its quotient.
* `PicSharp`, `PicSharp.functorial`, `PicSharp.presheaf` — the group-valued functor
  `(Over (Spec k))ᵒᵖ ⥤ AddCommGrpCat`, `T ↦ Pic(C ×_k T)`, with morphism action `g ↦ g^♯`
  descended from the line-bundle pullback `g_C^* = (id_C ×_k g)^*`.
* `PicSharp.relFunctorial`, `PicSharp.relPresheaf`, `PicSharp.toRelPresheaf` — the same
  functor on the `H_T`-coset carrier, and the natural quotient comparison from the
  absolute functor onto it.
* `PicSharp.etSheaf`, `PicSharp.etSheaf_group_structure` — the sheafification of
  `PicSharp.presheaf` for a Grothendieck topology `J` on `Over (Spec k)`, and its unit.

## Two carriers: absolute and relative

The setoid `RelPicPresheaf.preimage_subgroup` is the **iso-class** relation
`Nonempty (L.carrier ≅ L'.carrier)`, so `Quotient (RelPicPresheaf.preimage_subgroup πC πT)`
is the *absolute* Picard group `Pic(C ×_S T)` and `PicSharp` is the absolute functor — the
additive mirror of `picCommGroup`.  The *relative* functor of Kleiman `df:Pfs` lives on the
coarser carrier `Quotient (relPicSetoid πC πT) = Pic(C ×_S T) / π_T^* Pic(T)`; it is
`relPresheaf`, and `toRelPresheaf` is the comparison from the absolute functor.

The blueprint pins (`def:rel_pic_sharp` and friends) still name the absolute functor;
repinning them to the relative carrier is a coordinated blueprint change.  Likewise
`Picard/FGAPicRepresentability.lean` still uses its own opaque `Type u`-valued `picSharp`
placeholder; rewiring it to the functor built here needs a universe bump
(`Type u → Type (u + 1)` in `HasPicScheme` and downstream) and must target the
étale-sheafified *relative* functor — wiring it to the absolute `PicSharp` would make
`PicSharpRepresentable` a mathematically false statement.

## The `H_T`-coset relation

For `L L' : LineBundle.OnProduct πC πT`, `relPicRel` is taken in the multiplicative form
```
L ~ L'   ↔   ∃ N locally trivial on T,  L.carrier ≅ π_T^* N ⊗ L'.carrier,
```
the left-coset relation of `H_T := im π_T^*`.  It is equivalent to the blueprint's
`L ⊗ L'⁻¹ ≅ π_T^* N`, but avoids naming the tensor inverse of `L'` in the *definition*;
only the symmetry proof consumes a tensor inverse, that of `N` on the base `T`.

## The topology parameter

Mathlib does not provide an étale Grothendieck topology on schemes (only the morphism
property `AlgebraicGeometry.Etale`), so `PicSharp.etSheaf` takes the topology
`J : GrothendieckTopology (Over (Spec k))` as a parameter, to be specialised to the
canonical étale topology once that is available.  Sheafifying is not cosmetic:
`Pic^♯_{C/k}` is in general not representable (Kleiman L5105–L5108; see the §5
note below, and do **not** restore the older "not even a Zariski sheaf" reason,
which no source supports for the *relative* functor).

## References

Blueprint: `blueprint/src/chapters/Picard_RelPicFunctor.tex`.
Source: [Kleiman], "The Picard scheme", §2 (FGA Explained
Ch.9 §9.2), Definitions `df:aPf` (absolute Picard functor) +
`df:Pfs` (relative Picard functor, including the étale-sheafified form
`Pic_{(X/S)ét}`); Stacks Project tag 01CR (abelian-group structure on
the Picard group via tensor product).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme

namespace Modules

/-- **Restriction of `⊗` to the `LineBundle.OnProduct` carrier.**

For `S`-schemes `C, T`, the bifunctor `⊗_{C ×_S T}` restricts to the subtype
`LineBundle.OnProduct πC πT` of locally-trivial modules on `C ×_S T`, with unit
the structure sheaf and the dual as two-sided inverse. Per blueprint
`lem:tensorobj_lift_onproduct`: the carrier is `tensorObj L.carrier L'.carrier`, and
local triviality is `tensorObj_isLocallyTrivial`. -/
noncomputable def tensorObjOnProduct {S C T : Scheme.{u}} (πC : C ⟶ S) (πT : T ⟶ S)
    (L L' : LineBundle.OnProduct πC πT) : LineBundle.OnProduct πC πT :=
  ⟨tensorObj L.carrier L'.carrier,
    tensorObj_isLocallyTrivial L.isLocallyTrivial L'.isLocallyTrivial⟩

end Modules

namespace PicSharp

/-! ## §1. Abelian-group structure on the relative Picard quotient

The Picard group `Pic(X)` of any scheme is canonically an abelian group
under tensor product of line bundles (Stacks tag 01CR; the inverse of
`[L]` is `[L⁻¹] = [Hom_{O_X}(L, O_X)]`). The pullback map
`π_T^* : Pic(T) → Pic(C ×_k T)` of
`AlgebraicGeometry.Scheme.LineBundle.pullbackAlongProjection`
respects this structure: it sends `O_T ↦ O_{C ×_k T}` (the structure
sheaf is preserved by inverse image) and is multiplicative on tensor
products (Stacks 01HH for invertibility, Mathlib's
`Scheme.Modules.pullback` for the underlying multiplicativity).

Therefore `π_T^* Pic(T)` is a subgroup of `Pic(C ×_k T)`, and the
quotient `Pic(C ×_k T) / π_T^* Pic(T)` inherits a canonical
abelian-group structure under which the quotient map is a surjective
homomorphism with kernel exactly `π_T^* Pic(T)`.

Blueprint reference: `lem:rel_pic_sharp_groupoid` (Kleiman §2,
Defs. `df:aPf` + `df:Pfs`; Stacks tag 01CR). -/

/-! ### Substrate for the relative-Picard group law

The carrier setoid `RelPicPresheaf.preimage_subgroup` is the **iso-class** equivalence
`Nonempty (L.carrier ≅ L'.carrier)` on the locally-trivial line bundles on `C ×_S T`,
*not* the quotient-by-`H_T` relation. Hence `Quotient (preimage_subgroup πC πT)` is
`Pic(C ×_S T)` itself, and the `AddCommGroup` on it is the **tensor-product Picard
group** — the additive mirror of the absolute `picCommGroup`. The blueprint's Steps 2–4
(`pullbackHom`, `H_T := pullbackHom.range`, setoid reconciliation, transport) describe
the *other* carrier, the `H_T`-quotient built in §1b below; they do not apply to the
iso-class carrier.

The group law is built from the upstream substrate of `Picard/TensorObjSubstrate.lean`
(`Modules.tensorObj`, `Modules.tensorObjIsoOfIso`, the unitors, the braiding,
`Modules.tensorObj_assoc_iso`, `Modules.tensorObjOnProduct`,
`Modules.tensorObj_isLocallyTrivial`), not from a monoidal-category instance on
`Scheme.Modules`: `zero` is `isLocallyTrivial_unit`, and `neg`/`neg_add_cancel` use
`Modules.exists_tensorObj_inverse`, the reverse bridge
`IsLocallyTrivial ⟹ IsInvertible`. -/

/-- The structure sheaf is locally trivial (it restricts to the structure sheaf on
every affine open). On any affine chart `W ∋ x`: the restriction of the unit is
its pullback (`restrictFunctorIsoPullback`), and the pullback of the unit is the
unit (`pullbackUnitIso`); compose to trivialise `(𝒪_X)|_W ≅ 𝒪_W`. -/
private theorem isLocallyTrivial_unit {X : Scheme.{u}} :
    LineBundle.IsLocallyTrivial (SheafOfModules.unit X.ringCatSheaf) := by
  intro x
  obtain ⟨W, hW_aff, hxW, _⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤)
      (show x ∈ (⊤ : X.Opens) from trivial)
  refine ⟨W, hxW, hW_aff, ?_⟩
  exact ⟨(Scheme.Modules.restrictFunctorIsoPullback W.ι).app _ ≪≫ Modules.pullbackUnitIso W.ι⟩

/-- Uniqueness of the tensor inverse up to iso (mirror of `IsInvertible.inverse_unique`). -/
private theorem pInverseUnique {X : Scheme.{u}} {M N N' : X.Modules}
    (e : Modules.tensorObj M N ≅ SheafOfModules.unit X.ringCatSheaf)
    (e' : Modules.tensorObj M N' ≅ SheafOfModules.unit X.ringCatSheaf) :
    Nonempty (N ≅ N') :=
  ⟨(Modules.tensorObj_right_unitor N).symm ≪≫
    Modules.tensorObjIsoOfIso (Iso.refl N) e'.symm ≪≫
    (Modules.tensorObj_assoc_iso (M := N) (N := M) (P := N')).symm ≪≫
    Modules.tensorObjIsoOfIso (Modules.tensorObj_braiding N M ≪≫ e) (Iso.refl N') ≪≫
    Modules.tensorObj_left_unitor N'⟩

/-- The addition carrier: `[L] + [L'] := [L ⊗ L']`, lifted to the loc-triv carrier
`OnProduct`; this is `Modules.tensorObjOnProduct`. -/
private noncomputable def relTensorObj {S C T : Scheme.{u}} {πC : C ⟶ S} {πT : T ⟶ S}
    (L L' : LineBundle.OnProduct πC πT) : LineBundle.OnProduct πC πT :=
  Modules.tensorObjOnProduct πC πT L L'

/-- Descended addition on the relative Picard quotient: well-defined on iso-classes
by bifunctoriality (`Modules.tensorObjIsoOfIso`). Mirror of `picMul`. -/
private noncomputable def relAdd {S C T : Scheme.{u}} {πC : C ⟶ S} {πT : T ⟶ S} :
    Quotient (RelPicPresheaf.preimage_subgroup πC πT) →
      Quotient (RelPicPresheaf.preimage_subgroup πC πT) →
      Quotient (RelPicPresheaf.preimage_subgroup πC πT) :=
  Quotient.lift₂
    (fun L L' => Quotient.mk _ (relTensorObj L L'))
    (by
      rintro L L' M M' ⟨e⟩ ⟨e'⟩
      exact Quotient.sound ⟨Modules.tensorObjIsoOfIso e e'⟩)

/-- Descended negation on the relative Picard quotient: `-[L] := [Linv]` for the
inverse witness of `Modules.exists_tensorObj_inverse`, well-defined by
`pInverseUnique`. Mirror of `picInv`. -/
private noncomputable def relNeg {S C T : Scheme.{u}} {πC : C ⟶ S} {πT : T ⟶ S} :
    Quotient (RelPicPresheaf.preimage_subgroup πC πT) →
      Quotient (RelPicPresheaf.preimage_subgroup πC πT) :=
  Quotient.lift
    (fun L => Quotient.mk _
      (⟨Classical.choose (Modules.exists_tensorObj_inverse L.isLocallyTrivial),
        (Classical.choose_spec (Modules.exists_tensorObj_inverse L.isLocallyTrivial)).1⟩ :
        LineBundle.OnProduct πC πT))
    (by
      rintro L M ⟨e⟩
      refine Quotient.sound ?_
      have h1 :=
        (Classical.choose_spec (Modules.exists_tensorObj_inverse L.isLocallyTrivial)).2.some
      have h2 := Modules.tensorObjIsoOfIso e (Iso.refl _) ≪≫
        (Classical.choose_spec (Modules.exists_tensorObj_inverse M.isLocallyTrivial)).2.some
      exact pInverseUnique h1 h2)

/-- **Abelian-group instance on the ABSOLUTE Picard group** `Pic(C ×_S T)`.

For a base scheme `S`, a curve-side morphism `πC : C ⟶ S`, and a test
object `πT : T ⟶ S`, the quotient set
```
Quotient (RelPicPresheaf.preimage_subgroup πC πT)  =  Pic(C ×_S T)
```
is the set of **iso-classes** of locally-trivial line bundles on
`C ×_S T` — the carrier setoid `RelPicPresheaf.preimage_subgroup` is the
iso-class relation `Nonempty (L.carrier ≅ L'.carrier)`, NOT the coset
relation by `π_T^* Pic(T)`. So this is the absolute Picard group, the
additive mirror of `picCommGroup`; the RELATIVE quotient
`Pic(C ×_S T) / π_T^* Pic(T)` that `lem:rel_pic_sharp_groupoid` names is
`PicSharp.addCommGroup_via_tensorObj` on `Quotient (relPicSetoid πC πT)`
below.

It carries a canonical abelian-group structure: addition is the descent of
tensor product `[L] + [L'] := [L ⊗ L']`, the zero element is the class
`[O_{C ×_S T}]`, and the inverse is `-[L] := [L⁻¹]` (the dual line
bundle). The absolute group is consumed by the relative construction below.

The carrier `LineBundle.OnProduct` is `{ M : (pullback πC πT).Modules // IsLocallyTrivial M }`
(`LineBundlePullback.lean`), and the tensor-product group law is built directly from the
substrate of `AlgebraicJacobian/Picard/TensorObjSubstrate.lean` (`Modules.tensorObj`,
`Modules.tensorObjOnProduct`, the coherence isos
`Modules.tensorObj_{assoc_iso,left_unitor,right_unitor,braiding}`) — not from a
`Scheme.Modules` monoidal-category instance. `neg`/`neg_add_cancel` use
`Modules.exists_tensorObj_inverse`, the reverse bridge
`IsLocallyTrivial ⟹ IsInvertible`. -/
-- `nsmul`/`zsmul` carry no field default in `AddMonoid`/`SubNegMonoid`
-- (`Mathlib/Algebra/Group/Defs.lean:641`), and the canonical `nsmulRec`/`zsmulRec`
-- need `Zero`/`Add`/`Neg` instances that are not yet in scope mid-structure; we
-- supply them via `letI` so `nsmulRec`/`zsmulRec` elaborate (standard idiom).
noncomputable instance addCommGroup {S C T : Scheme.{u}}
    (πC : C ⟶ S) (πT : T ⟶ S) :
    AddCommGroup (Quotient (RelPicPresheaf.preimage_subgroup πC πT)) :=
  letI iZero : Zero (Quotient (RelPicPresheaf.preimage_subgroup πC πT)) :=
    ⟨Quotient.mk _ (⟨SheafOfModules.unit (Limits.pullback πC πT).ringCatSheaf,
      isLocallyTrivial_unit⟩ : LineBundle.OnProduct πC πT)⟩
  letI iAdd : Add (Quotient (RelPicPresheaf.preimage_subgroup πC πT)) := ⟨relAdd⟩
  letI iNeg : Neg (Quotient (RelPicPresheaf.preimage_subgroup πC πT)) := ⟨relNeg⟩
  { add := relAdd
    zero := Quotient.mk _
      (⟨SheafOfModules.unit (Limits.pullback πC πT).ringCatSheaf,
        isLocallyTrivial_unit⟩ : LineBundle.OnProduct πC πT)
    neg := relNeg
    nsmul := nsmulRec
    zsmul := zsmulRec
    add_assoc := by
      rintro a b c
      induction a using Quotient.ind with | _ a => ?_
      induction b using Quotient.ind with | _ b => ?_
      induction c using Quotient.ind with | _ c => ?_
      exact Quotient.sound
        ⟨Modules.tensorObj_assoc_iso (M := a.carrier) (N := b.carrier) (P := c.carrier)⟩
    zero_add := by
      rintro a
      induction a using Quotient.ind with | _ a => ?_
      exact Quotient.sound ⟨Modules.tensorObj_left_unitor a.carrier⟩
    add_zero := by
      rintro a
      induction a using Quotient.ind with | _ a => ?_
      exact Quotient.sound ⟨Modules.tensorObj_right_unitor a.carrier⟩
    neg_add_cancel := by
      rintro a
      induction a using Quotient.ind with | _ a => ?_
      exact Quotient.sound
        ⟨Modules.tensorObj_braiding _ a.carrier ≪≫
          (Classical.choose_spec (Modules.exists_tensorObj_inverse a.isLocallyTrivial)).2.some⟩
    add_comm := by
      rintro a b
      induction a using Quotient.ind with | _ a => ?_
      induction b using Quotient.ind with | _ b => ?_
      exact Quotient.sound ⟨Modules.tensorObj_braiding a.carrier b.carrier⟩ }

/-! ## §1b. The relative Picard `H_T`-coset setoid

`PicSharp.addCommGroup` lives on `Quotient (RelPicPresheaf.preimage_subgroup πC πT)`,
whose carrier setoid is the **iso-class** relation `Nonempty (L.carrier ≅ L'.carrier)` — i.e. the
**absolute** `Pic(C ×_S T)`. The blueprint (`lem:rel_pic_sharp_groupoid`, Kleiman §2 `df:Pfs`) asks
instead for the **relative** quotient `Pic(C ×_S T) / π_T^* Pic(T)`, the quotient by the subgroup
`H_T := im π_T^*`. This section builds that quotient directly as a coarser setoid
`relPicSetoid` on `LineBundle.OnProduct πC πT`, together with the abelian-group instance
`PicSharp.addCommGroup_via_tensorObj` on it.

**Relation (multiplicative form).** For `L L' : OnProduct πC πT` set
```
L ~ L'   ↔   ∃ N locally trivial on T,  L.carrier ≅ π_T^* N ⊗ L'.carrier,
```
where `π_T^* N = (LineBundle.pullbackAlongProjection πC πT N hN).carrier`. This is the left-coset
relation of `H_T := im π_T^*`. It is **equivalent** to the blueprint's `L ⊗ L'^{-1} ≅ π_T^* N`
(tensor both sides by `L'` / its inverse), but the multiplicative form avoids naming the tensor
inverse of `L'` in the *definition* — only the setoid-symmetry step consumes a tensor inverse (of
`N` on the base `T`, via `Modules.exists_tensorObj_inverse`). The blueprint statements
`lem:relpic_setoid_{refl,symm,trans}`, `lem:relpic_add_welldef` and `lem:pullback_inverse_iso`
are realized below in that multiplicative form. -/

/-- **The `H_T`-coset relation on `OnProduct πC πT`** (relative Picard, multiplicative form):
`L ~ L' ↔ ∃ N loc-triv on T, L.carrier ≅ π_T^* N ⊗ L'.carrier`. It encodes the
quotient `Pic(C ×_S T) / π_T^* Pic(T)` of `lem:rel_pic_sharp_groupoid`, and is coarser than the
absolute iso-class relation `RelPicPresheaf.preimage_subgroup`. -/
def relPicRel {S C T : Scheme.{u}} (πC : C ⟶ S) (πT : T ⟶ S)
    (L L' : LineBundle.OnProduct πC πT) : Prop :=
  ∃ (N : T.Modules) (hN : LineBundle.IsLocallyTrivial N),
    Nonempty (L.carrier ≅
      Modules.tensorObj (LineBundle.pullbackAlongProjection πC πT N hN).carrier L'.carrier)

/-- An isomorphism of the underlying bundles implies the `H_T`-coset relation (take `N = 𝒪_T`):
the relative relation is coarser than the absolute iso-class relation. Used to
transport the abelian-group axioms from the absolute iso-class group. -/
theorem relPicRel_of_iso {S C T : Scheme.{u}} {πC : C ⟶ S} {πT : T ⟶ S}
    {L L' : LineBundle.OnProduct πC πT} (e : Nonempty (L.carrier ≅ L'.carrier)) :
    relPicRel πC πT L L' := by
  obtain ⟨e⟩ := e
  refine ⟨SheafOfModules.unit T.ringCatSheaf, isLocallyTrivial_unit, ⟨?_⟩⟩
  exact e ≪≫ (Modules.tensorObj_left_unitor L'.carrier).symm ≪≫
    Modules.tensorObjIsoOfIso (Modules.pullbackUnitIso (Limits.pullback.snd πC πT)).symm
      (Iso.refl L'.carrier)

/-- **Reflexivity of the `H_T`-relation** (blueprint `lem:relpic_setoid_refl`): `L ~ L`, witnessed
by `N = 𝒪_T` and the pullback–unit iso `π_T^* 𝒪_T ≅ 𝒪_{C×T}` plus the left unitor. -/
theorem relPicRel_refl {S C T : Scheme.{u}} (πC : C ⟶ S) (πT : T ⟶ S)
    (L : LineBundle.OnProduct πC πT) : relPicRel πC πT L L :=
  relPicRel_of_iso ⟨Iso.refl _⟩

/-- **Symmetry of the `H_T`-relation** (blueprint `lem:relpic_setoid_symm`): from `L ~ L'` (via `N`)
get `L' ~ L` (via the tensor inverse `N⁻¹` on `T`), using multiplicativity of `π_T^*`, the
pullback–unit iso, and `Modules.exists_tensorObj_inverse`. -/
theorem relPicRel_symm {S C T : Scheme.{u}} {πC : C ⟶ S} {πT : T ⟶ S}
    {L L' : LineBundle.OnProduct πC πT} (h : relPicRel πC πT L L') :
    relPicRel πC πT L' L := by
  obtain ⟨N, hN, ⟨e⟩⟩ := h
  obtain ⟨Ninv, hNinv, ⟨eN⟩⟩ := Modules.exists_tensorObj_inverse hN
  refine ⟨Ninv, hNinv, ⟨?_⟩⟩
  -- `tensorObj (π_T^*Ninv) L ≅ L'`, then take `.symm`.
  refine Iso.symm ?_
  refine Modules.tensorObjIsoOfIso (Iso.refl _) e ≪≫ ?_
  refine (Modules.tensorObj_assoc_iso
    (M := (LineBundle.pullbackAlongProjection πC πT Ninv hNinv).carrier)
    (N := (LineBundle.pullbackAlongProjection πC πT N hN).carrier) (P := L'.carrier)).symm ≪≫ ?_
  refine Modules.tensorObjIsoOfIso
    (Modules.pullbackTensorIsoOfLocallyTrivial (Limits.pullback.snd πC πT) Ninv N hNinv hN).symm
    (Iso.refl L'.carrier) ≪≫ ?_
  refine Modules.tensorObjIsoOfIso
    ((Scheme.Modules.pullback (Limits.pullback.snd πC πT)).mapIso
      (Modules.tensorObj_braiding Ninv N ≪≫ eN)) (Iso.refl L'.carrier) ≪≫ ?_
  exact Modules.tensorObjIsoOfIso (Modules.pullbackUnitIso (Limits.pullback.snd πC πT))
    (Iso.refl L'.carrier) ≪≫ Modules.tensorObj_left_unitor L'.carrier

/-- **Transitivity of the `H_T`-relation** (blueprint `lem:relpic_setoid_trans`): from `L ~ L'` (via
`N`) and `L' ~ L''` (via `N'`) get `L ~ L''` via `N ⊗ N'`, using the associator and
multiplicativity of `π_T^*`. -/
theorem relPicRel_trans {S C T : Scheme.{u}} {πC : C ⟶ S} {πT : T ⟶ S}
    {L L' L'' : LineBundle.OnProduct πC πT}
    (h : relPicRel πC πT L L') (h' : relPicRel πC πT L' L'') :
    relPicRel πC πT L L'' := by
  obtain ⟨N, hN, ⟨e⟩⟩ := h
  obtain ⟨N', hN', ⟨e'⟩⟩ := h'
  refine ⟨Modules.tensorObj N N', Modules.tensorObj_isLocallyTrivial hN hN', ⟨?_⟩⟩
  refine e ≪≫ Modules.tensorObjIsoOfIso (Iso.refl _) e' ≪≫ ?_
  refine (Modules.tensorObj_assoc_iso
    (M := (LineBundle.pullbackAlongProjection πC πT N hN).carrier)
    (N := (LineBundle.pullbackAlongProjection πC πT N' hN').carrier) (P := L''.carrier)).symm ≪≫ ?_
  exact Modules.tensorObjIsoOfIso
    (Modules.pullbackTensorIsoOfLocallyTrivial (Limits.pullback.snd πC πT) N N' hN hN').symm
    (Iso.refl L''.carrier)

/-- **The relative Picard carrier setoid** `Pic(C ×_S T) / π_T^* Pic(T)` (blueprint
`lem:rel_pic_sharp_groupoid`, carrier), the `H_T`-coset relation on `LineBundle.OnProduct πC πT`.
This is the RELATIVE quotient, distinct from the absolute iso-class
setoid `RelPicPresheaf.preimage_subgroup`. -/
def relPicSetoid {S C T : Scheme.{u}} (πC : C ⟶ S) (πT : T ⟶ S) :
    Setoid (LineBundle.OnProduct πC πT) where
  r := relPicRel πC πT
  iseqv := ⟨relPicRel_refl πC πT, relPicRel_symm, relPicRel_trans⟩

/-- **The middle-four interchange for `⊗`** `(A ⊗ B) ⊗ (C ⊗ D) ≅ (A ⊗ C) ⊗ (B ⊗ D)`, assembled from
the associator and the braiding. Helper for `relPicRel_add`. -/
private noncomputable def tensorMiddleFour {X : Scheme.{u}} (A B C D : X.Modules) :
    Modules.tensorObj (Modules.tensorObj A B) (Modules.tensorObj C D) ≅
      Modules.tensorObj (Modules.tensorObj A C) (Modules.tensorObj B D) :=
  Modules.tensorObj_assoc_iso ≪≫
    Modules.tensorObjIsoOfIso (Iso.refl A)
      (Modules.tensorObj_assoc_iso (M := B) (N := C) (P := D)).symm ≪≫
    Modules.tensorObjIsoOfIso (Iso.refl A)
      (Modules.tensorObjIsoOfIso (Modules.tensorObj_braiding B C) (Iso.refl D)) ≪≫
    Modules.tensorObjIsoOfIso (Iso.refl A)
      (Modules.tensorObj_assoc_iso (M := C) (N := B) (P := D)) ≪≫
    (Modules.tensorObj_assoc_iso (M := A) (N := C) (P := Modules.tensorObj B D)).symm

/-- **Addition is well defined on the `H_T`-quotient** (blueprint `lem:relpic_add_welldef`): if
`L₁ ~ L₂` and `L₁' ~ L₂'` then `L₁ ⊗ L₁' ~ L₂ ⊗ L₂'`, via the middle-four interchange and
multiplicativity of `π_T^*`. -/
theorem relPicRel_add {S C T : Scheme.{u}} {πC : C ⟶ S} {πT : T ⟶ S}
    {L₁ L₂ L₁' L₂' : LineBundle.OnProduct πC πT}
    (h : relPicRel πC πT L₁ L₂) (h' : relPicRel πC πT L₁' L₂') :
    relPicRel πC πT (Modules.tensorObjOnProduct πC πT L₁ L₁')
      (Modules.tensorObjOnProduct πC πT L₂ L₂') := by
  obtain ⟨N, hN, ⟨e⟩⟩ := h
  obtain ⟨N', hN', ⟨e'⟩⟩ := h'
  refine ⟨Modules.tensorObj N N', Modules.tensorObj_isLocallyTrivial hN hN', ⟨?_⟩⟩
  -- `L₁ ⊗ L₁' ≅ (π_T^*N ⊗ L₂) ⊗ (π_T^*N' ⊗ L₂')`.
  refine Modules.tensorObjIsoOfIso e e' ≪≫ ?_
  -- middle-four → `(π_T^*N ⊗ π_T^*N') ⊗ (L₂ ⊗ L₂')`.
  refine tensorMiddleFour (LineBundle.pullbackAlongProjection πC πT N hN).carrier L₂.carrier
    (LineBundle.pullbackAlongProjection πC πT N' hN').carrier L₂'.carrier ≪≫ ?_
  -- multiplicativity of `π_T^*`: `π_T^*N ⊗ π_T^*N' ≅ π_T^*(N ⊗ N')`.
  exact Modules.tensorObjIsoOfIso
    (Modules.pullbackTensorIsoOfLocallyTrivial (Limits.pullback.snd πC πT) N N' hN hN').symm
    (Iso.refl (Modules.tensorObj L₂.carrier L₂'.carrier))

/-- The chosen tensor-inverse of `L` as an element of `OnProduct πC πT`, via
`Modules.exists_tensorObj_inverse`; it underlies negation on the relative Picard
quotient. -/
private noncomputable def relNegOnProduct {S C T : Scheme.{u}} {πC : C ⟶ S} {πT : T ⟶ S}
    (L : LineBundle.OnProduct πC πT) : LineBundle.OnProduct πC πT :=
  ⟨Classical.choose (Modules.exists_tensorObj_inverse L.isLocallyTrivial),
    (Classical.choose_spec (Modules.exists_tensorObj_inverse L.isLocallyTrivial)).1⟩

/-- **Negation is compatible with the `H_T`-relation** (blueprint `lem:relpic_setoid_symm`, negation
form): if `L ~ M` then their chosen tensor-inverses satisfy `L⁻¹ ~ M⁻¹`. The witness is `N⁻¹` on the
base `T`; both inverses are tensor-inverses of `L`, so they agree up to iso by `pInverseUnique`. -/
theorem relPicRel_neg {S C T : Scheme.{u}} {πC : C ⟶ S} {πT : T ⟶ S}
    {L M : LineBundle.OnProduct πC πT} (h : relPicRel πC πT L M) :
    relPicRel πC πT (relNegOnProduct L) (relNegOnProduct M) := by
  obtain ⟨N, hN, ⟨e⟩⟩ := h
  obtain ⟨Ninv, hNinv, ⟨eN⟩⟩ := Modules.exists_tensorObj_inverse hN
  refine ⟨Ninv, hNinv, ?_⟩
  have hLinv : Modules.tensorObj L.carrier (relNegOnProduct L).carrier ≅
      SheafOfModules.unit (Limits.pullback πC πT).ringCatSheaf :=
    (Classical.choose_spec (Modules.exists_tensorObj_inverse L.isLocallyTrivial)).2.some
  have hMinv : Modules.tensorObj M.carrier (relNegOnProduct M).carrier ≅
      SheafOfModules.unit (Limits.pullback πC πT).ringCatSheaf :=
    (Classical.choose_spec (Modules.exists_tensorObj_inverse M.isLocallyTrivial)).2.some
  have hOther : Modules.tensorObj L.carrier
      (Modules.tensorObj (LineBundle.pullbackAlongProjection πC πT Ninv hNinv).carrier
        (relNegOnProduct M).carrier) ≅
      SheafOfModules.unit (Limits.pullback πC πT).ringCatSheaf := by
    refine Modules.tensorObjIsoOfIso e (Iso.refl _) ≪≫ ?_
    refine tensorMiddleFour (LineBundle.pullbackAlongProjection πC πT N hN).carrier M.carrier
      (LineBundle.pullbackAlongProjection πC πT Ninv hNinv).carrier
      (relNegOnProduct M).carrier ≪≫ ?_
    refine Modules.tensorObjIsoOfIso
      (Modules.pullbackTensorIsoOfLocallyTrivial
        (Limits.pullback.snd πC πT) N Ninv hN hNinv).symm hMinv ≪≫ ?_
    refine Modules.tensorObjIsoOfIso
      ((Scheme.Modules.pullback (Limits.pullback.snd πC πT)).mapIso eN) (Iso.refl _) ≪≫ ?_
    refine Modules.tensorObjIsoOfIso (Modules.pullbackUnitIso (Limits.pullback.snd πC πT))
      (Iso.refl _) ≪≫ ?_
    exact Modules.tensorObj_left_unitor _
  exact pInverseUnique hLinv hOther

/-- Descended addition on the relative Picard quotient: `[L] + [L'] := [L ⊗ L']`, well-defined by
`relPicRel_add`. -/
private noncomputable def relAddVia {S C T : Scheme.{u}} {πC : C ⟶ S} {πT : T ⟶ S} :
    Quotient (relPicSetoid πC πT) → Quotient (relPicSetoid πC πT) →
      Quotient (relPicSetoid πC πT) :=
  Quotient.lift₂
    (fun L L' => Quotient.mk _ (Modules.tensorObjOnProduct πC πT L L'))
    (by
      rintro L L' M M' h h'
      exact Quotient.sound (relPicRel_add h h'))

/-- Descended negation on the relative Picard quotient: `-[L] := [L⁻¹]`, well-defined by
`relPicRel_neg`. -/
private noncomputable def relNegVia {S C T : Scheme.{u}} {πC : C ⟶ S} {πT : T ⟶ S} :
    Quotient (relPicSetoid πC πT) → Quotient (relPicSetoid πC πT) :=
  Quotient.lift
    (fun L => Quotient.mk _ (relNegOnProduct L))
    (by
      rintro L M h
      exact Quotient.sound (relPicRel_neg h))

/-- **Abelian-group structure on the RELATIVE Picard quotient** (blueprint
`lem:rel_pic_sharp_groupoid`; Kleiman §2 `df:Pfs`).

For a base `S`, a curve-side morphism `πC : C ⟶ S`, and a test object `πT : T ⟶ S`, the quotient
```
Quotient (relPicSetoid πC πT) = Pic(C ×_S T) / π_T^* Pic(T)
```
by the `H_T`-coset relation `relPicRel` carries a canonical abelian-group structure: addition is the
descent of tensor product `[L] + [L'] := [L ⊗ L']` (`relAddVia`, well-defined by `relPicRel_add`),
the zero element is the class `[𝒪_{C×_S T}]`, and the inverse is `-[L] := [L⁻¹]` (`relNegVia`,
well-defined by `relPicRel_neg`). Every abelian axiom transports from the objectwise coherence isos
along the quotient map, because `relPicRel` is coarser than the iso-class relation
(`relPicRel_of_iso`).

Distinct from `PicSharp.addCommGroup`, which is the ABSOLUTE `Pic(C ×_S T)` on the iso-class setoid
`RelPicPresheaf.preimage_subgroup`. As there, `neg`/`neg_add_cancel` use
`Modules.exists_tensorObj_inverse`, the reverse bridge `IsLocallyTrivial ⟹ IsInvertible`. -/
noncomputable instance addCommGroup_via_tensorObj {S C T : Scheme.{u}}
    (πC : C ⟶ S) (πT : T ⟶ S) :
    AddCommGroup (Quotient (relPicSetoid πC πT)) :=
  letI iZero : Zero (Quotient (relPicSetoid πC πT)) :=
    ⟨Quotient.mk _ (⟨SheafOfModules.unit (Limits.pullback πC πT).ringCatSheaf,
      isLocallyTrivial_unit⟩ : LineBundle.OnProduct πC πT)⟩
  letI iAdd : Add (Quotient (relPicSetoid πC πT)) := ⟨relAddVia⟩
  letI iNeg : Neg (Quotient (relPicSetoid πC πT)) := ⟨relNegVia⟩
  { add := relAddVia
    zero := Quotient.mk _
      (⟨SheafOfModules.unit (Limits.pullback πC πT).ringCatSheaf,
        isLocallyTrivial_unit⟩ : LineBundle.OnProduct πC πT)
    neg := relNegVia
    nsmul := nsmulRec
    zsmul := zsmulRec
    add_assoc := by
      rintro a b c
      induction a using Quotient.ind with | _ a => ?_
      induction b using Quotient.ind with | _ b => ?_
      induction c using Quotient.ind with | _ c => ?_
      exact Quotient.sound (relPicRel_of_iso
        ⟨Modules.tensorObj_assoc_iso (M := a.carrier) (N := b.carrier) (P := c.carrier)⟩)
    zero_add := by
      rintro a
      induction a using Quotient.ind with | _ a => ?_
      exact Quotient.sound (relPicRel_of_iso ⟨Modules.tensorObj_left_unitor a.carrier⟩)
    add_zero := by
      rintro a
      induction a using Quotient.ind with | _ a => ?_
      exact Quotient.sound (relPicRel_of_iso ⟨Modules.tensorObj_right_unitor a.carrier⟩)
    neg_add_cancel := by
      rintro a
      induction a using Quotient.ind with | _ a => ?_
      exact Quotient.sound (relPicRel_of_iso
        ⟨Modules.tensorObj_braiding _ a.carrier ≪≫
          (Classical.choose_spec (Modules.exists_tensorObj_inverse a.isLocallyTrivial)).2.some⟩)
    add_comm := by
      rintro a b
      induction a using Quotient.ind with | _ a => ?_
      induction b using Quotient.ind with | _ b => ?_
      exact Quotient.sound (relPicRel_of_iso ⟨Modules.tensorObj_braiding a.carrier b.carrier⟩) }

end PicSharp

/-! ## §3. Functoriality (group-homomorphism strengthening)

The naturality lemma `RelPicPresheaf.functorial` produces, for
each morphism `g : T' ⟶ T` over `S`, a set map
```
g^♯ : Pic(C ×_S T) ⟶ Pic(C ×_S T')
```
of quotient sets. Combined with the abelian-group instance of §1 on
both sides, this set map upgrades to an additive-monoid homomorphism
`AddMonoidHom`: indeed `g_C^*` preserves tensor products and the
structure sheaf, so it preserves the abelian-group operations on both
sides; the upgrade is the substantive content of
`lem:rel_pic_sharp_functorial`.

(§3 precedes §2 in the file because the functor `PicSharp` below
consumes `functorial` as its morphism action.)

Blueprint reference: `lem:rel_pic_sharp_functorial` (Kleiman §2,
Defs. `df:aPf` + `df:Pfs`). -/

namespace PicSharp

/-- **Functoriality of the relative Picard presheaf, group-hom form.**

For a base scheme `S`, a curve-side morphism `πC : C ⟶ S`, test objects
`πT : T ⟶ S` and `πT' : T' ⟶ S`, and a morphism `g : T' ⟶ T` over `S`
(encoded by `πT' = g ≫ πT`), the set map
`RelPicPresheaf.functorial πC πT πT' g hg` upgrades to an
`AddMonoidHom`-homomorphism with respect to the abelian-group structure
of `PicSharp.addCommGroup` on source and target.

The two homomorphism laws:

- `map_zero'` — pullback preserves the structure-sheaf class:
  `Modules.pullbackUnitIso` gives `g_C^* 𝒪_{C ×_S T} ≅ 𝒪_{C ×_S T'}`.
- `map_add'` — pullback preserves the tensor-product class: the loc-triv
  comparison iso `Modules.pullbackTensorIsoOfLocallyTrivial` gives
  `g_C^*(L ⊗ L') ≅ g_C^* L ⊗ g_C^* L'` on locally-trivial
  representatives. -/
noncomputable def functorial {S C T T' : Scheme.{u}}
    (πC : C ⟶ S) (πT : T ⟶ S) (πT' : T' ⟶ S) (g : T' ⟶ T)
    (hg : πT' = g ≫ πT) :
    Quotient (RelPicPresheaf.preimage_subgroup πC πT) →+
      Quotient (RelPicPresheaf.preimage_subgroup πC πT') where
  toFun := RelPicPresheaf.functorial πC πT πT' g hg
  map_zero' := Quotient.sound ⟨Modules.pullbackUnitIso _⟩
  map_add' a b := by
    induction a using Quotient.ind with | _ L => ?_
    induction b using Quotient.ind with | _ L' => ?_
    exact Quotient.sound
      ⟨Modules.pullbackTensorIsoOfLocallyTrivial _ L.carrier L'.carrier
        L.isLocallyTrivial L'.isLocallyTrivial⟩

/-- `functorial` at the identity is the identity: `id_C ×_S id_T` is the
identity of `C ×_S T` (`pullback.map_id`), and pullback along the identity
is naturally isomorphic to the identity functor (`Modules.pullbackId`). -/
private lemma functorial_id {S C T : Scheme.{u}}
    (πC : C ⟶ S) (πT : T ⟶ S) (hg : πT = 𝟙 T ≫ πT)
    (a : Quotient (RelPicPresheaf.preimage_subgroup πC πT)) :
    functorial πC πT πT (𝟙 T) hg a = a := by
  induction a using Quotient.ind with | _ L => ?_
  refine Quotient.sound ⟨(Scheme.Modules.pullbackCongr ?_).app L.carrier ≪≫
    (Scheme.Modules.pullbackId _).app L.carrier⟩
  apply Limits.pullback.hom_ext <;> simp

/-- `functorial` is contravariantly compositional: `(h ≫ g)_C = h_C ≫ g_C`
(`pullback.hom_ext` chase), and pullback along a composite is the composite
of the pullbacks (`Modules.pullbackComp`). -/
private lemma functorial_comp {S C T T' T'' : Scheme.{u}}
    (πC : C ⟶ S) (πT : T ⟶ S) (πT' : T' ⟶ S) (πT'' : T'' ⟶ S)
    (g : T' ⟶ T) (h : T'' ⟶ T') (hg : πT' = g ≫ πT) (hh : πT'' = h ≫ πT')
    (hgh : πT'' = (h ≫ g) ≫ πT)
    (a : Quotient (RelPicPresheaf.preimage_subgroup πC πT)) :
    functorial πC πT πT'' (h ≫ g) hgh a
      = functorial πC πT' πT'' h hh (functorial πC πT πT' g hg a) := by
  induction a using Quotient.ind with | _ L => ?_
  refine Quotient.sound ⟨(Scheme.Modules.pullbackCongr ?_).app L.carrier ≪≫
    (Scheme.Modules.pullbackComp _ _).symm.app L.carrier⟩
  apply Limits.pullback.hom_ext <;>
    simp [Limits.pullback.lift_fst, Limits.pullback.lift_snd,
      Limits.pullback.lift_snd_assoc]

end PicSharp

/-! ## §2. The relative Picard presheaf as a group-valued functor

We assemble the data of `LineBundlePullback.lean` (object-level quotient set,
`RelPicPresheaf.functorial` morphism action) and §1 (abelian-group
instance on each quotient) into a single contravariant functor

```
PicSharp_{C/k} : (Over (Spec k))^op ⥤ AddCommGrpCat
```

sending an `Spec k`-scheme `T` to the abelian group `Pic(C ×_k T)`
(with the structure of §1; see the §1 note — the carrier setoid is the
iso-class relation, i.e. the ABSOLUTE Picard group of the product; the
`H_T`-coset version is `relPresheaf` in §4b), and a morphism
`g : T' ⟶ T` over `Spec k` to the group homomorphism
`g^♯ : Pic^♯_{C/k}(T) → Pic^♯_{C/k}(T')` descended from the
line-bundle pullback `g_C^* := (id_C ×_k g)^*`.

Blueprint reference: `def:rel_pic_sharp` (Kleiman §2, Def. `df:Pfs`). -/

/-- The **relative Picard functor** of a smooth proper geometrically
integral curve `C` over a field `k`, as a contravariant functor

```
PicSharp_{C/k} : (Over (Spec k))^op ⥤ AddCommGrpCat
```

On objects: `T ↦ Pic(C ×_k T)`, the tensor-product Picard group of the
product (Lean instance `PicSharp.addCommGroup`; the carrier setoid is
the iso-class relation — the ABSOLUTE Picard group — see the §1 note;
the `H_T`-coset version is `relPresheaf` in §4b).

On morphisms: `g ↦ g^♯`, the group homomorphism descended from
`g_C^* = (id_C ×_k g)^*` via the quotient (the set-level map is
`RelPicPresheaf.functorial`; the group-hom upgrade is
`PicSharp.functorial` above). Identity and composition laws are
`PicSharp.functorial_id` / `PicSharp.functorial_comp`, i.e.
`Modules.pullbackId` / `Modules.pullbackComp` descended through the
quotient.

Universe: object map values are `AddCommGrpCat.{u+1}` because the
underlying carrier `Quotient (preimage_subgroup πC πT)` lives in
`Type (u+1)` (since `LineBundle.OnProduct` is defined to land in
`Type (u+1)`). -/
noncomputable def PicSharp {k : Type u} [Field k] (_C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 _C.hom] [IsProper _C.hom] :
    (Over (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u+1} where
  obj T := AddCommGrpCat.of
    (Quotient (RelPicPresheaf.preimage_subgroup _C.hom T.unop.hom))
  map {T T'} g := AddCommGrpCat.ofHom
    (PicSharp.functorial _C.hom T.unop.hom T'.unop.hom g.unop.left
      (Over.w g.unop).symm)
  map_id T := by
    ext a
    exact PicSharp.functorial_id _C.hom T.unop.hom _ a
  map_comp {T T' T''} g h := by
    ext a
    exact PicSharp.functorial_comp _C.hom T.unop.hom T'.unop.hom T''.unop.hom
      g.unop.left h.unop.left (Over.w g.unop).symm (Over.w h.unop).symm _ a

namespace PicSharp

/-! ## §4. Wrapping as a functor instance

The group-valued presheaf bundling: combine the on-objects assignment
of `PicSharp` (carrying the `addCommGroup` structure) with the
on-morphisms assignment of `functorial` (each a group hom) into a
single functor `(Over (Spec k))^op ⥤ AddCommGrpCat`. The identity /
composition laws of the functor are inherited from the corresponding
identities on `Scheme.Modules.pullback`, descended through the
quotient.

This wrapper is kept distinct from `PicSharp` to mirror the blueprint
split (`def:rel_pic_sharp` vs.\ `thm:rel_pic_sharp_presheaf`) and to
record the explicit re-packaging step from the lemma-by-lemma data
(`addCommGroup`, `PicSharp`, `functorial`) into a single
category-theoretic functor — useful when applying functorial
constructions (Yoneda, sheafification, …) to the *bundled* form.

Blueprint reference: `thm:rel_pic_sharp_presheaf` (Kleiman §2,
Defs. `df:aPf` + `df:Pfs`). -/

/-- **The relative Picard presheaf, bundled.**

The relative Picard functor `PicSharp_{C/k}` packaged as a single
contravariant functor `(Over (Spec k))^op ⥤ AddCommGrpCat`, with object
action `T ↦ Pic(C ×_k T)` (group structure `PicSharp.addCommGroup`) and
morphism action `g ↦ g^♯` (group hom from `PicSharp.functorial`).
Identity and composition laws are inherited from
`Scheme.Modules.pullbackId` / `Scheme.Modules.pullbackComp` descended
through the quotient.

The body is `PicSharp _C`: the on-objects/on-morphisms data of §2 already
produces a functor into `AddCommGrpCat.{u+1}`. The split between the
"object/morphism description" (`PicSharp`) and the "bundled functor"
(`presheaf`) mirrors the blueprint partition `def:rel_pic_sharp` /
`thm:rel_pic_sharp_presheaf`; on the Lean side they are the same data.

Note on naming: this is the canonical "fully assembled" form mentioned
as `thm:rel_pic_sharp_presheaf` in the blueprint; it is structurally a
`def` (not a `theorem`) because the conclusion is a `Functor` (data),
not a `Prop`. -/
noncomputable def presheaf {k : Type u} [Field k] (_C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 _C.hom] [IsProper _C.hom] :
    (Over (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u+1} :=
  PicSharp _C

/-! ## §4b. The RELATIVE Picard functor on the `H_T`-quotient

The §1b substrate (`relPicSetoid`, `addCommGroup_via_tensorObj`) supplies the
relative carrier `Pic(C ×_S T) / π_T^* Pic(T)`. Here we equip it with
the same pullback functoriality as the absolute functor above, giving the
relative Picard presheaf `relPresheaf` of Kleiman `df:Pfs`, and
the natural quotient comparison `toRelPresheaf` from the absolute functor.

Well-definedness across `H_T`-cosets is the extra content: for a coset witness
`N` with `L ≅ π_T^* N ⊗ L'`, the comparison iso
(`Modules.pullbackTensorIsoOfLocallyTrivial`) and the pullback square
`LineBundle.pullback_pullback_eq` (`g_C^* π_T^* N ≅ π_{T'}^* g^* N`) produce
the witness `g^* N` for `g_C^* L ~ g_C^* L'`. -/

/-- The base-change morphism `g_C := id_C ×_S g : C ×_S T' ⟶ C ×_S T` of a
test morphism `g : T' ⟶ T` over `S` (the `pullback.map` used throughout the
functorial actions of this chapter). -/
noncomputable def baseChangeOverC {S C T T' : Scheme.{u}}
    (πC : C ⟶ S) (πT : T ⟶ S) (πT' : T' ⟶ S) (g : T' ⟶ T)
    (hg : πT' = g ≫ πT) :
    Limits.pullback πC πT' ⟶ Limits.pullback πC πT :=
  Limits.pullback.map πC πT' πC πT (𝟙 C) g (𝟙 S)
    (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hg])

/-- **Pullback descends to the `H_T`-quotient** (well-definedness of the
relative functorial action): if `L ~ L'` via the coset witness `N`, then
`g_C^* L ~ g_C^* L'` via the coset witness `g^* N`. The iso chain is
`g_C^* L ≅ g_C^*(π_T^* N ⊗ L') ≅ g_C^* π_T^* N ⊗ g_C^* L'
≅ π_{T'}^*(g^* N) ⊗ g_C^* L'` (functoriality,
`pullbackTensorIsoOfLocallyTrivial`, `pullback_pullback_eq`). -/
theorem relPicRel_pullback {S C T T' : Scheme.{u}}
    {πC : C ⟶ S} {πT : T ⟶ S} {πT' : T' ⟶ S} {g : T' ⟶ T}
    {hg : πT' = g ≫ πT} {L L' : LineBundle.OnProduct πC πT}
    (h : relPicRel πC πT L L') :
    relPicRel πC πT'
      ⟨(Scheme.Modules.pullback (baseChangeOverC πC πT πT' g hg)).obj L.carrier,
        L.isLocallyTrivial.pullback _⟩
      ⟨(Scheme.Modules.pullback (baseChangeOverC πC πT πT' g hg)).obj L'.carrier,
        L'.isLocallyTrivial.pullback _⟩ := by
  obtain ⟨N, hN, ⟨e⟩⟩ := h
  refine ⟨(Scheme.Modules.pullback g).obj N, hN.pullback g, ⟨?_⟩⟩
  refine (Scheme.Modules.pullback (baseChangeOverC πC πT πT' g hg)).mapIso e ≪≫ ?_
  refine Modules.pullbackTensorIsoOfLocallyTrivial _ _ _
    (LineBundle.pullbackAlongProjection πC πT N hN).isLocallyTrivial
    L'.isLocallyTrivial ≪≫ ?_
  exact Modules.tensorObjIsoOfIso
    (LineBundle.pullback_pullback_eq πC πT πT' g hg N).some (Iso.refl _)

/-- **Functoriality on the RELATIVE `H_T`-quotient, group-hom form**
(blueprint `lem:rel_pic_sharp_functorial`, honest relative carrier). For a
test morphism `g : T' ⟶ T` over `S`, the pullback `[L] ↦ [g_C^* L]` descends
to the `H_T`-coset quotients (`relPicRel_pullback`) and is a group
homomorphism (structure-sheaf and tensor preservation, exactly as in the
absolute `functorial`). -/
noncomputable def relFunctorial {S C T T' : Scheme.{u}}
    (πC : C ⟶ S) (πT : T ⟶ S) (πT' : T' ⟶ S) (g : T' ⟶ T)
    (hg : πT' = g ≫ πT) :
    Quotient (relPicSetoid πC πT) →+ Quotient (relPicSetoid πC πT') where
  toFun := Quotient.lift
    (fun L : LineBundle.OnProduct πC πT =>
      Quotient.mk (relPicSetoid πC πT')
        (⟨(Scheme.Modules.pullback (baseChangeOverC πC πT πT' g hg)).obj L.carrier,
          L.isLocallyTrivial.pullback _⟩ : LineBundle.OnProduct πC πT'))
    (fun _ _ h => Quotient.sound (relPicRel_pullback h))
  map_zero' := Quotient.sound (relPicRel_of_iso ⟨Modules.pullbackUnitIso _⟩)
  map_add' a b := by
    induction a using Quotient.ind with | _ L => ?_
    induction b using Quotient.ind with | _ L' => ?_
    exact Quotient.sound (relPicRel_of_iso
      ⟨Modules.pullbackTensorIsoOfLocallyTrivial _ L.carrier L'.carrier
        L.isLocallyTrivial L'.isLocallyTrivial⟩)

/-- `relFunctorial` at the identity is the identity (`pullback.map_id` +
`Modules.pullbackId` descended through the `H_T`-quotient). -/
private lemma relFunctorial_id {S C T : Scheme.{u}}
    (πC : C ⟶ S) (πT : T ⟶ S) (hg : πT = 𝟙 T ≫ πT)
    (a : Quotient (relPicSetoid πC πT)) :
    relFunctorial πC πT πT (𝟙 T) hg a = a := by
  induction a using Quotient.ind with | _ L => ?_
  refine Quotient.sound (relPicRel_of_iso
    ⟨(Scheme.Modules.pullbackCongr ?_).app L.carrier ≪≫
      (Scheme.Modules.pullbackId _).app L.carrier⟩)
  apply Limits.pullback.hom_ext <;> simp [baseChangeOverC]

/-- `relFunctorial` is contravariantly compositional (`pullback.hom_ext`
chase + `Modules.pullbackComp` descended through the `H_T`-quotient). -/
private lemma relFunctorial_comp {S C T T' T'' : Scheme.{u}}
    (πC : C ⟶ S) (πT : T ⟶ S) (πT' : T' ⟶ S) (πT'' : T'' ⟶ S)
    (g : T' ⟶ T) (h : T'' ⟶ T') (hg : πT' = g ≫ πT) (hh : πT'' = h ≫ πT')
    (hgh : πT'' = (h ≫ g) ≫ πT)
    (a : Quotient (relPicSetoid πC πT)) :
    relFunctorial πC πT πT'' (h ≫ g) hgh a
      = relFunctorial πC πT' πT'' h hh (relFunctorial πC πT πT' g hg a) := by
  induction a using Quotient.ind with | _ L => ?_
  refine Quotient.sound (relPicRel_of_iso
    ⟨(Scheme.Modules.pullbackCongr ?_).app L.carrier ≪≫
      (Scheme.Modules.pullbackComp _ _).symm.app L.carrier⟩)
  apply Limits.pullback.hom_ext <;>
    simp [baseChangeOverC, Limits.pullback.lift_fst, Limits.pullback.lift_snd,
      Limits.pullback.lift_snd_assoc]

/-- **The RELATIVE Picard presheaf** `T ↦ Pic(C ×_k T) / π_T^* Pic(T)` as a
group-valued functor — the Kleiman `df:Pfs` object, on the
`H_T`-coset carrier `Quotient (relPicSetoid _C.hom T.unop.hom)` with the
group structure `addCommGroup_via_tensorObj` and the pullback-descended
morphism action `relFunctorial`. The absolute functor `PicSharp` above
compares onto it via the quotient map `toRelPresheaf`. -/
noncomputable def relPresheaf {k : Type u} [Field k] (_C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 _C.hom] [IsProper _C.hom] :
    (Over (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u+1} where
  obj T := AddCommGrpCat.of (Quotient (relPicSetoid _C.hom T.unop.hom))
  map {T T'} g := AddCommGrpCat.ofHom
    (relFunctorial _C.hom T.unop.hom T'.unop.hom g.unop.left (Over.w g.unop).symm)
  map_id T := by
    ext a
    exact relFunctorial_id _C.hom T.unop.hom _ a
  map_comp {T T' T''} g h := by
    ext a
    exact relFunctorial_comp _C.hom T.unop.hom T'.unop.hom T''.unop.hom
      g.unop.left h.unop.left (Over.w g.unop).symm (Over.w h.unop).symm _ a

/-- **The quotient comparison** `Pic(C ×_k T) ⟶ Pic(C ×_k T)/π_T^* Pic(T)`,
natural in `T`: the componentwise `H_T`-coset quotient map from the absolute
functor `PicSharp` to the relative functor `relPresheaf` (a group
homomorphism because the group laws on both sides descend the same tensor
operations; the `H_T`-relation is coarser than the iso-class relation by
`relPicRel_of_iso`). -/
noncomputable def toRelPresheaf {k : Type u} [Field k] (_C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 _C.hom] [IsProper _C.hom] :
    PicSharp _C ⟶ relPresheaf _C where
  app T := AddCommGrpCat.ofHom
    { toFun := Quotient.lift
        (fun L => Quotient.mk (relPicSetoid _C.hom T.unop.hom) L)
        (fun _ _ e => Quotient.sound (relPicRel_of_iso e))
      map_zero' := rfl
      map_add' := by
        rintro ⟨a⟩ ⟨b⟩
        rfl }
  naturality {T T'} g := by
    ext a
    induction a using Quotient.ind with | _ L => ?_
    rfl

end PicSharp

/-! ## §5. Étale sheafification

The relative Picard presheaf `PicSharp_{C/k}` is not *a priori* a sheaf
(Kleiman §2, L1330), and over a general field it is **not representable**:
Kleiman L5105–L5108 states this for the conic `u²+v²+w²=0` in `ℙ²_ℝ`, a smooth
plane conic and hence smooth, proper and geometrically integral over a field with
no rational point. In Lean that step is
`PicScheme.not_exists_representing_picSharp_of_not_isIso`
(`Picard/PicEtSubcanonical.lean`), whose one open input is that the comparison
really fails for that conic.

(**Two citations have been wrong in this slot, both corrected 2026-07-29.** "§2
L1292–L1302", which stood here for weeks, is about the *absolute* functor
`Pic_X` — the relative one quotients by `Pic(T)` precisely to defeat that
argument. Its first replacement, `ex:Pfs`, compares the two *sheafifications*, so
it does not show `picSharp` failing Zariski descent either; `th:cmp` part 1 in
fact gives `picSharp ↪ Pic_{(X/S)zar}` here. Do not rebuild the argument through
a sheaf condition. Full account in `Picard/FGAPicRepresentability.lean`'s module
docstring.)

To obtain a representable
functor in the sense of `chap:Picard_FGAPicRepresentability`, one
replaces `PicSharp_{C/k}` by its **associated étale sheaf**
`Pic^♯_{(C/k)ét} := (PicSharp_{C/k})^{∼ét}`. Kleiman §4
(Theorem `th:main`) represents precisely this sheafified functor.

The sheafification is encoded as `presheafToSheaf J _` applied to the
bundled `PicSharp.presheaf`, for a **parameter** Grothendieck topology
`J` on `Over (Spec k)`, because Mathlib does not ship an étale
Grothendieck topology on schemes (only the morphism property
`AlgebraicGeometry.Etale`); `J` is to be bound to the canonical étale
topology once that is available.

*Naming note*: the blueprint pins this declaration under
`AlgebraicGeometry.Scheme.PicScheme`, which already names the
*representing scheme* in `Picard/FGAPicRepresentability.lean`, so the
namespaced name `PicSharp.etSheaf` is used here instead.

Blueprint reference: `def:rel_pic_etale_sheafification` (Kleiman §2,
`df:Pfs` étale-sheaf clause). -/

/-- The **étale sheafification of the relative Picard presheaf**.

Given a smooth proper geometrically integral curve `C` over a field
`k`, and a Grothendieck topology `J` on `Over (Spec k)` (intended: the
canonical étale topology on `(Sch/k)`), the **étale-sheafified relative
Picard functor**

```
Pic^♯_{(C/k)ét} := (PicSharp_{C/k})^{~_ét}
```

is the sheafification of the group-valued presheaf
`PicSharp.presheaf` of `thm:rel_pic_sharp_presheaf`. Equivalently, it is
the unique (up to canonical isomorphism) sheaf of abelian groups on the
site `(Over (Spec k), J)` equipped with a presheaf morphism
`PicSharp.presheaf ⟶ (forget _) ∘ -` universal among presheaf morphisms
to abelian-group sheaves.

Encoded as a `Sheaf J AddCommGrpCat.{u+1}` object, with body
`(CategoryTheory.presheafToSheaf J AddCommGrpCat).obj (PicSharp.presheaf _C)`
(Mathlib's `Sites.ConcreteSheafification`), parametric in the topology
`J`; the `HasWeakSheafify` instance for an abelian-group target and an
arbitrary Grothendieck topology comes from
`Mathlib.CategoryTheory.Sites.Sheafification`.

Note that this sheafifies the ABSOLUTE functor `PicSharp.presheaf`; the
étale sheafification of the relative functor `relPresheaf` is what the
downstream representability statement needs.

In Kleiman's notation with `X = C` and `S = Spec k`, this is
`Pic_{(X/S)ét}` from `df:Pfs`. -/
noncomputable def PicSharp.etSheaf {k : Type u} [Field k] (_C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 _C.hom] [IsProper _C.hom]
    (J : GrothendieckTopology (Over (Spec (.of k)))) :
    Sheaf J AddCommGrpCat.{u+1} :=
  (CategoryTheory.presheafToSheaf J AddCommGrpCat.{u+1}).obj (PicSharp.presheaf _C)

namespace PicSharp

/-! ## §6. Sheafification preserves the abelian-group structure

The étale sheafification of an abelian-group-valued presheaf is itself
abelian-group-valued: the forgetful functor `AddCommGrpCat ⥤ Type`
preserves filtered colimits (these are computed pointwise), and the
plus-construction is built from filtered colimits, so sheafification
commutes with the forgetful functor up to canonical isomorphism. The
substantive content is the **sheafification unit**: a canonical
morphism of presheaves `PicSharp.presheaf ⟶ (PicSharp.etSheaf ?).obj`
(in `AddCommGrpCat`) that exhibits the universal property of
sheafification.

The blueprint's `thm:rel_pic_etale_sheaf_group_structure` is a
description rather than a Lean target; the unit is surfaced here so
that the downstream representability statement
(`chap:Picard_FGAPicRepresentability`) can cite it directly.

Blueprint reference: `thm:rel_pic_etale_sheaf_group_structure` (Kleiman
§2, `df:Pfs`; standard `Sheafification.toSheafify` content). -/

/-- **Sheafification unit for the étale Picard sheafification.**

Given the étale-sheafified relative Picard functor
`PicSharp.etSheaf C J : Sheaf J AddCommGrpCat`, there is a canonical
morphism of (group-valued) presheaves
```
η_C : PicSharp.presheaf C ⟶ (PicSharp.etSheaf C J).obj
```
in the functor category `(Over (Spec k))^op ⥤ AddCommGrpCat`.

The witness is the **universal sheafification unit**
`toSheafify J (PicSharp.presheaf C)` — the unit of Mathlib's
`sheafificationAdjunction` at the Picard presheaf, i.e. the canonical
comparison map `Pic^♯_{C/k} ⟶ Pic^♯_{(C/k)ét}` through which every
morphism to an étale sheaf factors. -/
theorem etSheaf_group_structure {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    (J : GrothendieckTopology (Over (Spec (.of k)))) :
    Nonempty (PicSharp.presheaf C ⟶ (PicSharp.etSheaf C J).obj) :=
  ⟨CategoryTheory.toSheafify J (PicSharp.presheaf C)⟩

end PicSharp

end Scheme

end AlgebraicGeometry
