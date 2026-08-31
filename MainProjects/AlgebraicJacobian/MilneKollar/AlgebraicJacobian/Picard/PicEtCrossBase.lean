/-
Copyright (c) 2026 Axel Delaval. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval
-/
import Mathlib
import AlgebraicJacobian.Picard.PicEtSheaf
import AlgebraicJacobian.RiemannRoch.CurveBaseChange

/-!
# The cross-base identification for `picEt` — input 2 of the repaired descent route

This file addresses `AJC.picrep.etale-rep.crossbase`, the input that
`review-ajc` measured (`I-1076`) as missing from every site that prices the
repaired representability route, and as *upstream* of the Galois step rather
than beside it.

## What obligation this is

The seam sorry `fgaPicardRepresentability`
(`Picard/FGAPicRepresentability.lean`) is discharged, on the committed
Milne–Kollár route, by descending `PicScheme.picEt` from a separably closed
extension. The descent needs the `k'`-scheme produced over `k'` to represent
`picEt` **of the base-changed curve** `C_{k'}`. What the construction actually
hands you is `picEt` **of the `k`-curve `C`, restricted to `k'`-tests**. Those
are *a priori* different functors on `(Sch/k')`, and if they are not
identified there is no functor for a Galois descent datum to be a datum *for* —
a mismatch no green build would reveal, since both sides typecheck.

So the obligation is: for finite separable `k'/k` and a `k'`-test `T`,

```
picEt (C_{k'})  ≅  (Over.map φ).op ⋙ picEt C          (φ : Spec k' ⟶ Spec k)
```

as functors on `(Sch/k')ᵒᵖ`.

## What this file proves, and what it does not

**The whole sheafification layer of the obligation is FREE**, and that is the
result here. `picEt` is a *categorical* sheafification, and Mathlib's
`Functor.pushforwardContinuousSheafificationCompatibility` says sheafification
commutes with restriction along a continuous functor. Restriction along
`Over.map φ` *is* continuous for the two localised étale topologies (by
synthesis — `§1`), so the sheaf-level identification reduces, with no residue,
to the same statement one level down at the *unsheafified* relative Picard
presheaf (`§5`). That reduction is the content: it converts a statement about
an object defined by a universal property into a statement about an explicit
quotient of line-bundle classes.

**The presheaf-level face is CLOSED too, so the identification is proved
outright** (`picEt_crossBaseIso`, `§6`) — this file has no `sorry`. Its four
layers:

* the two total spaces are canonically isomorphic (`§2`, `crossBaseTotalIso`),
  by the single Mathlib lemma `pullbackLeftPullbackSndIso`;
* the `H_T`-coset *relation* transports across that iso in **both** directions,
  with the **same** coset witness `N` (`§3`, `crossBase_relPicRel` and
  `crossBase_relPicRel_inv`) — this is the layer where the two subgroups being
  quotiented by have to correspond, and it is the substantive one;
* hence the two relative Picard groups are in canonical **bijection** for every
  test (`crossBaseQuotEquiv`): the round trips reduce, through
  `relPicRel_of_iso`, to `crossBaseTotalIso`'s own `hom_inv_id`/`inv_hom_id`.
  It is additive (`crossBaseQuotMap_add`) because addition is descended tensor
  and pullback preserves tensor products of locally trivial bundles;
* and it is **natural in the test** (`crossBaseQuotMap_relFunctorial`), which is
  what upgrades the family of bijections to an isomorphism of functors — the
  distinction that matters, since `§5`'s reduction consumes an `Iso`, not a
  family of `Equiv`s. Naturality reduces to
  `pullbackLeftPullbackSndIso_naturality`, which holds in **any** category with
  pullbacks: no geometry, no field, no curve.

**Nothing here closes the seam sorry, and no antecedent of
`fgaPicardRepresentability` is witnessed for any curve by this file** — that
distinction is the point of the round's bar. What is closed is one *input of the
route*, in full and unconditionally; what remains open is the seam obligation
itself. The route's other inputs are the descent test
(`Picard/EtaleFieldCover.lean`, landed), `G1`/`G2` (whose single remaining gate
is `HasGaloisQuotient`), and — below all three — a section over separably closed
fields, which `I-1135` measured as having no producer in this project at all.
So the repair has **four** inputs, not three, and this file closes one of them.

## Why not port the sibling project's version

`Algebraic-Jacobian-Challenge-Rebuild` proves a cross-base comparison as a
`MulEquiv` (`picEtCrossBaseEquiv`, `Picard/PicEtCrossBase.lean:316`, 468
lines). It is **not importable and not transcribable**: that project's `picEt`
is a hand-built limit of plus-classes over affine opens, this one's is a
categorical sheafification, and there is no `lake` edge between the projects.
Most of its length is a section-ring scalar tower which — as `review-ajc`
predicted, and as the outcome here confirms — a sheafification-based `picEt`
does not need: the sheafification layer is discharged by a Mathlib compatibility
iso instead. The 468 lines were a design lead, and the lead was that they are
not the seam. **For the record, measured rather than estimated: ~711 lines, of
which ~330 comment, ~275 code, ~106 blank** — so a little over half is prose, not
"the great majority" as an earlier revision of this sentence guessed. The proof
terms are short because each layer lands on a Mathlib lemma. Reading the sibling
as a lead rather than transcribing its 468 lines was the cheaper move.

## Measurement discipline

Every synthesis claim below was checked with `lake build` first (oleans fresh,
EXIT=0, 8681 jobs for this module) — a stale-import environment reports every probe as
succeeding (`I-1057`). The continuity claim of `§1` carries a control: the
strictly stronger `IsDenseSubsite` at the *same* two topologies does **not**
synthesize, so the pushforward is not an equivalence and the compatibility iso
of `§5` is not a triviality.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits

namespace AlgebraicGeometry

namespace Scheme

namespace PicScheme

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']

/-! ## §1. The restriction functor on tests, and its continuity -/

/-- The structural morphism `Spec k' ⟶ Spec k` of a field extension. -/
noncomputable abbrev specMapAlgebra (k : Type u) [Field k] (k' : Type u) [Field k']
    [Algebra k k'] : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k k'))

/-- **Restriction of tests along `k ⊆ k'`**: a `k'`-scheme `T` is in particular
a `k`-scheme, via `T ⟶ Spec k' ⟶ Spec k`. This is the functor along which the
descent step compares the two Picard functors. -/
noncomputable abbrev restrictTest (k : Type u) [Field k] (k' : Type u) [Field k']
    [Algebra k k'] : Over (Spec (CommRingCat.of k')) ⥤ Over (Spec (CommRingCat.of k)) :=
  Over.map (specMapAlgebra k k')

/-- `restrictTest` acts as the identity on the underlying scheme of a test. -/
@[simp]
theorem restrictTest_obj_left (T : Over (Spec (CommRingCat.of k'))) :
    ((restrictTest k k').obj T).left = T.left := rfl

/-- `restrictTest` composes the structure morphism with `φ`, by definition. -/
@[simp]
theorem restrictTest_obj_hom (T : Over (Spec (CommRingCat.of k'))) :
    ((restrictTest k k').obj T).hom = T.hom ≫ specMapAlgebra k k' := rfl

/-- **Restriction of tests is continuous** for the two localised étale
topologies `etaleTopologyOver k'` and `etaleTopologyOver k`.

This is Mathlib's general instance for `Over.map` between localisations of one
topology (`GrothendieckTopology.over`), and it is what makes the sheafification
layer of the cross-base identification free — see `picEt_crossBaseIso_of_relPresheaf`.

**Not a triviality**: the strictly stronger `IsDenseSubsite` at the same two
topologies does *not* synthesize (measured, control for this claim), so the
induced pushforward on sheaves is not an equivalence. -/
instance restrictTest_isContinuous :
    (restrictTest k k').IsContinuous
      (etaleTopologyOver k') (etaleTopologyOver k) :=
  inferInstance

/-! ## §2. The geometric heart: cancellation of the intermediate base -/

/-- **The two total spaces agree.** For a `k'`-test `T`, the curve base-changed
to `k'` and then producted with `T` over `k'` is the same scheme as the
original `k`-curve producted with `T` over `k`:

```
C_{k'} ×_{Spec k'} T  ≅  C ×_{Spec k} T
```

This is the geometric content of the cross-base identification, and it is a
single Mathlib lemma: `baseChangeField C k'` is by definition the pullback of
`C.hom` along `φ`, so this is base-cancellation
(`pullbackLeftPullbackSndIso`) for the composite `T.hom ≫ φ`.

Note the right-hand side is literally the product formed by the *restricted*
test: `((restrictTest k k').obj T).hom` is `T.hom ≫ φ` by definition
(`restrictTest_obj_hom`), so this iso compares exactly the two schemes whose
Picard groups the two sides of the obligation take. -/
noncomputable def crossBaseTotalIso (C : Over (Spec (CommRingCat.of k)))
    (T : Over (Spec (CommRingCat.of k'))) :
    pullback (baseChangeField C k').hom T.hom
      ≅ pullback C.hom ((restrictTest k k').obj T).hom :=
  pullbackLeftPullbackSndIso C.hom (specMapAlgebra k k') T.hom

/-- The cancellation iso is compatible with the projection to the test: both
sides' second projections are the map to `T.left`. -/
@[simp]
theorem crossBaseTotalIso_hom_snd (C : Over (Spec (CommRingCat.of k)))
    (T : Over (Spec (CommRingCat.of k'))) :
    (crossBaseTotalIso C T).hom ≫ pullback.snd C.hom ((restrictTest k k').obj T).hom
      = pullback.snd (baseChangeField C k').hom T.hom :=
  pullbackLeftPullbackSndIso_hom_snd _ _ _

/-! ## §3. The `H_T`-coset relation transports across the base change

The two carriers of the presheaf-level face are `H_T`-coset quotients of
line bundles on the two total spaces of `§2`. This section proves that
`crossBaseTotalIso` carries the coset *relation* to the coset relation — which
is the step where the two subgroups being quotiented by have to correspond, and
therefore the load-bearing part of the presheaf face. -/

/-- **Pullback along the total-space iso matches the two projection pullbacks.**

`crossBaseTotalIso C T` was built by base-cancellation, so composing it with
the projection to `T` on the `C_{k'}`-side gives the projection to `T` on the
`C`-side (`pullbackLeftPullbackSndIso_inv_snd_snd`). Hence pulling a bundle
back from `T` and then along the iso is the same as pulling it back from `T`
directly.

This is what makes the subgroups `H_T = im π_T^*` on the two sides correspond,
and it is stated at *functor* level deliberately: the object-level form sends
`isDefEq` into a heartbeat blow-up on these pullback towers, while the functor
form is immediate. -/
noncomputable def crossBaseProjPullbackIso (C : Over (Spec (CommRingCat.of k)))
    (T : Over (Spec (CommRingCat.of k'))) :
    Scheme.Modules.pullback (pullback.snd (baseChangeField C k').hom T.hom)
        ⋙ Scheme.Modules.pullback (crossBaseTotalIso C T).inv
      ≅ Scheme.Modules.pullback (pullback.snd C.hom ((restrictTest k k').obj T).hom) :=
  Scheme.Modules.pullbackComp _ _ ≪≫
    Scheme.Modules.pullbackCongr
      (pullbackLeftPullbackSndIso_inv_snd_snd C.hom (specMapAlgebra k k') T.hom)

/-- **Transport of a relative line bundle across the base change**: a line
bundle on `C_{k'} ×_{k'} T` becomes one on `C ×_k T` by pullback along
`crossBaseTotalIso`, local triviality being preserved
(`IsLocallyTrivial.pullback`). -/
noncomputable def crossBaseOnProduct (C : Over (Spec (CommRingCat.of k)))
    (T : Over (Spec (CommRingCat.of k')))
    (L : LineBundle.OnProduct (baseChangeField C k').hom T.hom) :
    LineBundle.OnProduct C.hom ((restrictTest k k').obj T).hom :=
  ⟨(Scheme.Modules.pullback (crossBaseTotalIso C T).inv).obj L.carrier,
    L.isLocallyTrivial.pullback _⟩

/-- **The `H_T`-coset relation is preserved by the cross-base transport.**

If `L ~ L'` on `C_{k'} ×_{k'} T` with coset witness `N` on `T`, then the
transported bundles are related on `C ×_k T` **with the same witness `N`** —
the witness does not change, because both sides quotient by the pullback of
`Pic(T)` along projections that `crossBaseProjPullbackIso` identifies.

This is the substantive half of the presheaf-level face: it says the two
quotients are quotients of isomorphic groups by *corresponding* subgroups. -/
theorem crossBase_relPicRel (C : Over (Spec (CommRingCat.of k)))
    (T : Over (Spec (CommRingCat.of k')))
    {L L' : LineBundle.OnProduct (baseChangeField C k').hom T.hom}
    (h : PicSharp.relPicRel (baseChangeField C k').hom T.hom L L') :
    PicSharp.relPicRel C.hom ((restrictTest k k').obj T).hom
      (crossBaseOnProduct C T L) (crossBaseOnProduct C T L') := by
  obtain ⟨N, hN, ⟨e⟩⟩ := h
  refine ⟨N, hN, ⟨?_⟩⟩
  refine (Scheme.Modules.pullback (crossBaseTotalIso C T).inv).mapIso e ≪≫ ?_
  refine Modules.pullbackTensorIsoOfLocallyTrivial _ _ _
    (LineBundle.pullbackAlongProjection _ _ N hN).isLocallyTrivial
    L'.isLocallyTrivial ≪≫ ?_
  exact Modules.tensorObjIsoOfIso ((crossBaseProjPullbackIso C T).app N) (Iso.refl _)

/-- The **mirror transport**, along `crossBaseTotalIso.hom`: a line bundle on
`C ×_k T` becomes one on `C_{k'} ×_{k'} T`. Same construction as
`crossBaseOnProduct` in the other direction; both are needed for bijectivity. -/
noncomputable def crossBaseOnProductInv (C : Over (Spec (CommRingCat.of k)))
    (T : Over (Spec (CommRingCat.of k')))
    (L : LineBundle.OnProduct C.hom ((restrictTest k k').obj T).hom) :
    LineBundle.OnProduct (baseChangeField C k').hom T.hom :=
  ⟨(Scheme.Modules.pullback (crossBaseTotalIso C T).hom).obj L.carrier,
    L.isLocallyTrivial.pullback _⟩

/-- The mirror of `crossBaseProjPullbackIso`, in the `hom` direction, from
`crossBaseTotalIso_hom_snd`. -/
noncomputable def crossBaseProjPullbackIsoInv (C : Over (Spec (CommRingCat.of k)))
    (T : Over (Spec (CommRingCat.of k'))) :
    Scheme.Modules.pullback (pullback.snd C.hom ((restrictTest k k').obj T).hom)
        ⋙ Scheme.Modules.pullback (crossBaseTotalIso C T).hom
      ≅ Scheme.Modules.pullback (pullback.snd (baseChangeField C k').hom T.hom) :=
  Scheme.Modules.pullbackComp _ _ ≪≫
    Scheme.Modules.pullbackCongr (crossBaseTotalIso_hom_snd C T)

/-- **The mirror relation transport.** Symmetric to `crossBase_relPicRel`, with
the same coset witness, via `crossBaseProjPullbackIsoInv`. -/
theorem crossBase_relPicRel_inv (C : Over (Spec (CommRingCat.of k)))
    (T : Over (Spec (CommRingCat.of k')))
    {L L' : LineBundle.OnProduct C.hom ((restrictTest k k').obj T).hom}
    (h : PicSharp.relPicRel C.hom ((restrictTest k k').obj T).hom L L') :
    PicSharp.relPicRel (baseChangeField C k').hom T.hom
      (crossBaseOnProductInv C T L) (crossBaseOnProductInv C T L') := by
  obtain ⟨N, hN, ⟨e⟩⟩ := h
  refine ⟨N, hN, ⟨?_⟩⟩
  refine (Scheme.Modules.pullback (crossBaseTotalIso C T).hom).mapIso e ≪≫ ?_
  refine Modules.pullbackTensorIsoOfLocallyTrivial _ _ _
    (LineBundle.pullbackAlongProjection _ _ N hN).isLocallyTrivial
    L'.isLocallyTrivial ≪≫ ?_
  exact Modules.tensorObjIsoOfIso ((crossBaseProjPullbackIsoInv C T).app N) (Iso.refl _)

/-- **Round trip on carriers, `inv` then `hom`**: transporting a bundle to the
`C ×_k T` side and back returns an isomorphic bundle. Composition of pullbacks
plus `crossBaseTotalIso.hom_inv_id`.

Stated on carriers rather than on `OnProduct` because the local-triviality field
is a `Prop` and plays no part. -/
noncomputable def crossBaseRoundTripCarrier (C : Over (Spec (CommRingCat.of k)))
    (T : Over (Spec (CommRingCat.of k')))
    (L : LineBundle.OnProduct (baseChangeField C k').hom T.hom) :
    (crossBaseOnProductInv C T (crossBaseOnProduct C T L)).carrier ≅ L.carrier :=
  (Scheme.Modules.pullbackComp _ _).app L.carrier ≪≫
    (Scheme.Modules.pullbackCongr (crossBaseTotalIso C T).hom_inv_id).app L.carrier ≪≫
      (Scheme.Modules.pullbackId _).app L.carrier

/-- Round trip the other way, from `crossBaseTotalIso.inv_hom_id`. -/
noncomputable def crossBaseRoundTripCarrier' (C : Over (Spec (CommRingCat.of k)))
    (T : Over (Spec (CommRingCat.of k')))
    (L : LineBundle.OnProduct C.hom ((restrictTest k k').obj T).hom) :
    (crossBaseOnProduct C T (crossBaseOnProductInv C T L)).carrier ≅ L.carrier :=
  (Scheme.Modules.pullbackComp _ _).app L.carrier ≪≫
    (Scheme.Modules.pullbackCongr (crossBaseTotalIso C T).inv_hom_id).app L.carrier ≪≫
      (Scheme.Modules.pullbackId _).app L.carrier

/-- **The induced map of relative Picard carriers**, one test at a time:
`Pic(C_{k'} ×_{k'} T)/π_T^* Pic(T) ⟶ Pic(C ×_k T)/π_T^* Pic(T)`.

Well defined by `crossBase_relPicRel`. This is the componentwise map of the
presheaf-level face; it is upgraded to a bijection by `crossBaseQuotEquiv`, shown
additive by `crossBaseQuotMap_add`, and shown natural in `T` by
`crossBaseQuotMap_relFunctorial` — which together give the functor isomorphism
`relPresheafCrossBaseIso`. -/
noncomputable def crossBaseQuotMap (C : Over (Spec (CommRingCat.of k)))
    (T : Over (Spec (CommRingCat.of k'))) :
    Quotient (PicSharp.relPicSetoid (baseChangeField C k').hom T.hom) →
      Quotient (PicSharp.relPicSetoid C.hom ((restrictTest k k').obj T).hom) :=
  Quotient.lift
    (fun L => Quotient.mk _ (crossBaseOnProduct C T L))
    (fun _ _ h => Quotient.sound (crossBase_relPicRel C T h))

/-- The mirror quotient map, from `crossBase_relPicRel_inv`. -/
noncomputable def crossBaseQuotMapInv (C : Over (Spec (CommRingCat.of k)))
    (T : Over (Spec (CommRingCat.of k'))) :
    Quotient (PicSharp.relPicSetoid C.hom ((restrictTest k k').obj T).hom) →
      Quotient (PicSharp.relPicSetoid (baseChangeField C k').hom T.hom) :=
  Quotient.lift
    (fun L => Quotient.mk _ (crossBaseOnProductInv C T L))
    (fun _ _ h => Quotient.sound (crossBase_relPicRel_inv C T h))

/-- **`crossBaseQuotMapInv` is a left inverse of `crossBaseQuotMap`.** On a
class `⟦L⟧`, the round trip returns `⟦L''⟧` with `L''.carrier ≅ L.carrier`
(`crossBaseRoundTripCarrier`), and an isomorphism of underlying bundles implies
the `H_T`-coset relation (`relPicRel_of_iso`, take `N = 𝒪_T`) — so the two
classes are equal. -/
theorem crossBaseQuotMapInv_crossBaseQuotMap (C : Over (Spec (CommRingCat.of k)))
    (T : Over (Spec (CommRingCat.of k')))
    (x : Quotient (PicSharp.relPicSetoid (baseChangeField C k').hom T.hom)) :
    crossBaseQuotMapInv C T (crossBaseQuotMap C T x) = x := by
  induction x using Quotient.ind with | _ L => ?_
  exact Quotient.sound (PicSharp.relPicRel_of_iso ⟨crossBaseRoundTripCarrier C T L⟩)

/-- **…and a right inverse**, by the mirror round trip. -/
theorem crossBaseQuotMap_crossBaseQuotMapInv (C : Over (Spec (CommRingCat.of k)))
    (T : Over (Spec (CommRingCat.of k')))
    (x : Quotient (PicSharp.relPicSetoid C.hom ((restrictTest k k').obj T).hom)) :
    crossBaseQuotMap C T (crossBaseQuotMapInv C T x) = x := by
  induction x using Quotient.ind with | _ L => ?_
  exact Quotient.sound (PicSharp.relPicRel_of_iso ⟨crossBaseRoundTripCarrier' C T L⟩)

/-- **The cross-base identification of relative Picard carriers, one test at a
time — an EQUIVALENCE.**

This is the pointwise half of the presheaf-level face, and it is now proved
rather than assumed: the two relative Picard groups

```
Pic(C_{k'} ×_{k'} T) / π_T^* Pic(T)   and   Pic(C ×_k T) / π_T^* Pic(T)
```

are in canonical bijection for every `k'`-test `T`.

**Bijectivity alone is not the presheaf face.** A pointwise family of bijections
is not an isomorphism of functors and cannot be fed to the sheafification
reduction of `§5`, whose hypothesis is an `Iso`. What upgrades this family is
`crossBaseQuotMap_add` (additivity) together with
`crossBaseQuotMap_relFunctorial` (naturality in `T`), both proved below; the
assembled functor isomorphism is `relPresheafCrossBaseIso`. -/
noncomputable def crossBaseQuotEquiv (C : Over (Spec (CommRingCat.of k)))
    (T : Over (Spec (CommRingCat.of k'))) :
    Quotient (PicSharp.relPicSetoid (baseChangeField C k').hom T.hom) ≃
      Quotient (PicSharp.relPicSetoid C.hom ((restrictTest k k').obj T).hom) where
  toFun := crossBaseQuotMap C T
  invFun := crossBaseQuotMapInv C T
  left_inv := crossBaseQuotMapInv_crossBaseQuotMap C T
  right_inv := crossBaseQuotMap_crossBaseQuotMapInv C T

/-! ### The naturality square, at scheme level

The remaining layer of the presheaf face is that the pointwise bijection commutes
with base change in the test. That reduces to one identity of maps between
pullbacks, and it holds in **any** category with pullbacks — no geometry, no
field, no curve. It is stated at that generality below precisely because that is
what its proof uses. -/

/-- **Base cancellation is natural in the test object**, in an arbitrary
category with pullbacks.

For `f : X ⟶ S`, `φ : S' ⟶ S` and a map of `S'`-objects `g : (T', t') ⟶ (T, t)`,
the square

```
  (X ×_S S') ×_{S'} T'  ──iso──▶  X ×_S T'
        │ pullback.map g                │ pullback.map g
        ▼                               ▼
  (X ×_S S') ×_{S'} T   ──iso──▶  X ×_S T
```

commutes, where both horizontal maps are `pullbackLeftPullbackSndIso`. Proved by
`pullback.hom_ext` from the iso's two projection identities.

This is the naturality input the cross-base identification needs; it is
formulated generically because the argument is entirely about pullback
projections. -/
theorem pullbackLeftPullbackSndIso_naturality {D : Type*} [Category D]
    [Limits.HasPullbacks D] {X S : D} (f : X ⟶ S) {S' : D} (φ : S' ⟶ S)
    {T T' : D} (t : T ⟶ S') (t' : T' ⟶ S') (g : T' ⟶ T) (hg : t' = g ≫ t) :
    pullback.map (pullback.snd f φ) t' (pullback.snd f φ) t (𝟙 _) g (𝟙 _)
        (by simp) (by simp [hg])
        ≫ (pullbackLeftPullbackSndIso f φ t).hom
      = (pullbackLeftPullbackSndIso f φ t').hom
        ≫ pullback.map f (t' ≫ φ) f (t ≫ φ) (𝟙 _) g (𝟙 _) (by simp)
            (by simp [hg]) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullbackLeftPullbackSndIso_hom_fst,
      pullback.lift_fst, pullback.lift_fst_assoc, pullback.map, Category.comp_id]
  · simp only [Category.assoc, pullbackLeftPullbackSndIso_hom_snd,
      pullback.lift_snd, pullback.map, Category.comp_id]
    simp

/-- **The naturality square for `crossBaseTotalIso`**, in the project's own
spelling: the cancellation iso commutes with the base-change morphisms
`PicSharp.baseChangeOverC` that `relFunctorial` acts by.

This is `pullbackLeftPullbackSndIso_naturality` applied at
`f = C.hom`, `φ = Spec k' ⟶ Spec k` — it needs no separate argument, because
`baseChangeOverC` is by definition the `pullback.map` of the generic lemma and
`crossBaseTotalIso` is by definition its `pullbackLeftPullbackSndIso`. -/
theorem crossBaseTotalIso_naturality (C : Over (Spec (CommRingCat.of k)))
    (T T' : Over (Spec (CommRingCat.of k'))) (g : T' ⟶ T) :
    PicSharp.baseChangeOverC (baseChangeField C k').hom T.hom T'.hom g.left
          (Over.w g).symm
        ≫ (crossBaseTotalIso C T).hom
      = (crossBaseTotalIso C T').hom
        ≫ PicSharp.baseChangeOverC C.hom ((restrictTest k k').obj T).hom
            ((restrictTest k k').obj T').hom g.left
            (Over.w ((restrictTest k k').map g)).symm :=
  pullbackLeftPullbackSndIso_naturality C.hom (specMapAlgebra k k') T.hom T'.hom
    g.left (Over.w g).symm

/-- The `inv`-direction form of `crossBaseTotalIso_naturality`, which is the
orientation the transport of bundles uses (bundles pull back along `inv`). -/
theorem crossBaseTotalIso_inv_naturality (C : Over (Spec (CommRingCat.of k)))
    (T T' : Over (Spec (CommRingCat.of k'))) (g : T' ⟶ T) :
    (crossBaseTotalIso C T').inv
        ≫ PicSharp.baseChangeOverC (baseChangeField C k').hom T.hom T'.hom g.left
            (Over.w g).symm
      = PicSharp.baseChangeOverC C.hom ((restrictTest k k').obj T).hom
            ((restrictTest k k').obj T').hom g.left
            (Over.w ((restrictTest k k').map g)).symm
        ≫ (crossBaseTotalIso C T).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  exact crossBaseTotalIso_naturality C T T' g

/-- **The pointwise bijection is NATURAL in the test.**

`crossBaseQuotEquiv` commutes with the base-change action
`PicSharp.relFunctorial`, i.e. the square drawn at
`relPresheaf_crossBaseIso` below commutes. On a class `⟦L⟧` both routes pull
`L.carrier` back along composites of scheme maps that
`crossBaseTotalIso_inv_naturality` shows are equal, and `Modules.pullbackComp`
turns each composite into the corresponding composite of pullbacks. -/
theorem crossBaseQuotMap_relFunctorial (C : Over (Spec (CommRingCat.of k)))
    (T T' : Over (Spec (CommRingCat.of k'))) (g : T' ⟶ T)
    (x : Quotient (PicSharp.relPicSetoid (baseChangeField C k').hom T.hom)) :
    crossBaseQuotMap C T'
        (PicSharp.relFunctorial (baseChangeField C k').hom T.hom T'.hom g.left
          (Over.w g).symm x)
      = PicSharp.relFunctorial C.hom ((restrictTest k k').obj T).hom
          ((restrictTest k k').obj T').hom g.left
          (Over.w ((restrictTest k k').map g)).symm (crossBaseQuotMap C T x) := by
  induction x using Quotient.ind with | _ L => ?_
  refine Quotient.sound (PicSharp.relPicRel_of_iso ⟨?_⟩)
  refine (Scheme.Modules.pullbackComp _ _).app L.carrier ≪≫ ?_
  exact (Scheme.Modules.pullbackCongr
      (crossBaseTotalIso_inv_naturality C T T' g)).app L.carrier ≪≫
    ((Scheme.Modules.pullbackComp _ _).app L.carrier).symm

/-- **The transport is additive.** Addition on the relative Picard quotient is
descended tensor product, and pullback along any morphism carries a tensor
product of locally trivial bundles to the tensor product of the pullbacks
(`Modules.pullbackTensorIsoOfLocallyTrivial`) — so the transport respects it. -/
theorem crossBaseQuotMap_add (C : Over (Spec (CommRingCat.of k)))
    (T : Over (Spec (CommRingCat.of k')))
    (x y : Quotient (PicSharp.relPicSetoid (baseChangeField C k').hom T.hom)) :
    crossBaseQuotMap C T (x + y)
      = crossBaseQuotMap C T x + crossBaseQuotMap C T y := by
  induction x using Quotient.ind with | _ L => ?_
  induction y using Quotient.ind with | _ L' => ?_
  exact Quotient.sound (PicSharp.relPicRel_of_iso
    ⟨Modules.pullbackTensorIsoOfLocallyTrivial _ _ _ L.isLocallyTrivial
      L'.isLocallyTrivial⟩)

/-- The component of the cross-base identification as a **group** isomorphism,
which is what a morphism of `AddCommGrpCat`-valued presheaves requires. -/
noncomputable def crossBaseQuotAddEquiv (C : Over (Spec (CommRingCat.of k)))
    (T : Over (Spec (CommRingCat.of k'))) :
    Quotient (PicSharp.relPicSetoid (baseChangeField C k').hom T.hom) ≃+
      Quotient (PicSharp.relPicSetoid C.hom ((restrictTest k k').obj T).hom) where
  __ := crossBaseQuotEquiv C T
  map_add' := crossBaseQuotMap_add C T

/-! ## §4. The presheaf-level face — now PROVED -/

/-- **The cross-base identification at the level of the UNSHEAFIFIED relative
Picard presheaf** — proved here, and proved rather than assumed anywhere
downstream. Earlier revisions of this docstring described it as the one statement
the file left open; that was true of those revisions and is false of this one.

What it says: the relative Picard presheaf of the base-changed curve `C_{k'}`,
as a functor on `k'`-tests, agrees with the relative Picard presheaf of `C`
evaluated on restricted tests.

**What is already proved, and what precisely remains.** On a fixed test `T` the
two carriers are `Pic(C_{k'} ×_{k'} T)/π_T^* Pic(T)` and
`Pic(C ×_k T)/π_T^* Pic(T)`, and above they are shown to be **in canonical
bijection** (`crossBaseQuotEquiv`) — total-space iso, relation transport both
ways, both round trips.

**Naturality — the last layer — is `crossBaseQuotMap_relFunctorial`**: the
square

```
  Pic^rel(C_{k'} ×_{k'} T)  ──crossBaseQuotEquiv──▶  Pic^rel(C ×_k T)
          │ relFunctorial(g)                                │ relFunctorial(g)
          ▼                                                 ▼
  Pic^rel(C_{k'} ×_{k'} T') ──crossBaseQuotEquiv──▶  Pic^rel(C ×_k T')
```

commutes for every test morphism `g : T' ⟶ T`. Both vertical maps are pullback
along a `pullback.map` and the horizontal ones are pullback along the
cancellation iso, so the content is that those commute — which
`pullbackLeftPullbackSndIso_naturality` establishes in **any** category with
pullbacks, by `pullback.hom_ext` from the iso's two projection identities. No
geometry enters.

**So this statement is now PROVED rather than assumed**, and the `sorry` is
gone: the group-homomorphism property of each component is inherited from
`relFunctorial`'s own additivity, since `crossBaseQuotMap` is built by
`Quotient.lift` of a tensor-compatible transport. -/
noncomputable def relPresheafCrossBaseIso (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] (k' : Type u) [Field k']
    [Algebra k k'] :
    PicSharp.relPresheaf (baseChangeField C k')
      ≅ (restrictTest k k').op ⋙ PicSharp.relPresheaf C :=
  NatIso.ofComponents
    (fun T =>
      { hom := AddCommGrpCat.ofHom (crossBaseQuotAddEquiv C T.unop).toAddMonoidHom
        inv := AddCommGrpCat.ofHom (crossBaseQuotAddEquiv C T.unop).symm.toAddMonoidHom
        hom_inv_id := by
          ext x
          exact (crossBaseQuotAddEquiv C T.unop).symm_apply_apply x
        inv_hom_id := by
          ext x
          exact (crossBaseQuotAddEquiv C T.unop).apply_symm_apply x })
    (fun {T T'} g => by
      ext x
      exact crossBaseQuotMap_relFunctorial C T.unop T'.unop g.unop x)

/-- The `Nonempty` form, which is what a downstream consumer that only needs
existence of the identification should cite. -/
theorem relPresheaf_crossBaseIso (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] (k' : Type u) [Field k']
    [Algebra k k'] :
    Nonempty (PicSharp.relPresheaf (baseChangeField C k')
      ≅ (restrictTest k k').op ⋙ PicSharp.relPresheaf C) :=
  ⟨relPresheafCrossBaseIso C k'⟩

/-! ## §5. The reduction: sheafification adds nothing -/

/-- **The sheafification layer of the cross-base identification is free.**

Given the identification at the level of the unsheafified relative Picard
presheaf, the identification for the étale-sheafified functor
`PicSharp.etaleSheaf` follows with no further geometric input.

The mechanism: `picEt` is defined by *categorical* sheafification, and
sheafification commutes with restriction along a continuous functor
(`Functor.pushforwardContinuousSheafificationCompatibility`), while restriction
along `restrictTest` is continuous for the two localised étale topologies
(`restrictTest_isContinuous`). The underlying presheaf of the resulting
pushforward is *definitionally* the restriction, which is what lets the
composite be read as a statement about `etaleSheaf` directly.

This is the declaration that prices the obligation: it says the descent route's
input 2 costs the presheaf-level face and nothing more. -/
noncomputable def etaleSheaf_crossBaseIso_of_relPresheaf
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    (D : Over (Spec (CommRingCat.of k')))
    [SmoothOfRelativeDimension 1 D.hom] [IsProper D.hom]
    (e : PicSharp.relPresheaf D ≅ (restrictTest k k').op ⋙ PicSharp.relPresheaf C) :
    (PicSharp.etaleSheaf D).obj ≅ (restrictTest k k').op ⋙ (PicSharp.etaleSheaf C).obj :=
  (sheafToPresheaf _ _).mapIso
    ((presheafToSheaf (etaleTopologyOver k') AddCommGrpCat.{u+1}).mapIso e ≪≫
      ((restrictTest k k').pushforwardContinuousSheafificationCompatibility
        AddCommGrpCat.{u+1} (etaleTopologyOver k') (etaleTopologyOver k)).app
        (PicSharp.relPresheaf C))

/-- **The cross-base identification for `picEt` itself**, i.e. for the
set-valued functor whose representability is the seam obligation
`fgaPicardRepresentability`.

Same content as `etaleSheaf_crossBaseIso_of_relPresheaf`, pushed through the
forgetful functor: `picEt` is `etaleSheaf ⋙ forget`, and whiskering an iso is
an iso. Stated separately because `picEt`, not the group-valued sheaf, is the
functor the seam's `RepresentableBy` clause is about.

**This is the implication half, stated separately from its discharge.** Its
hypothesis `e` is the presheaf-level identification, which `§4` *proves*
(`relPresheafCrossBaseIso`); it is taken as an explicit argument here rather than
synthesized so that the sheafification step is usable against any presheaf-level
iso, not only that one. The composite with the proof supplied is
`picEt_crossBaseIso` in `§6`. -/
noncomputable def picEt_crossBaseIso_of_relPresheaf
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    (D : Over (Spec (CommRingCat.of k')))
    [SmoothOfRelativeDimension 1 D.hom] [IsProper D.hom]
    (e : PicSharp.relPresheaf D ≅ (restrictTest k k').op ⋙ PicSharp.relPresheaf C) :
    picEt D ≅ (restrictTest k k').op ⋙ picEt C :=
  Functor.isoWhiskerRight (etaleSheaf_crossBaseIso_of_relPresheaf C D e)
      (CategoryTheory.forget AddCommGrpCat.{u+1}) ≪≫
    Functor.associator _ _ _

/-- The reduction, specialised to the base-changed curve — the shape the
descent step actually consumes. The base-changed curve inherits both binders
(`smoothOfRelativeDimension_one_hom_baseChangeField`,
`isProper_hom_baseChangeField`), so no hypothesis on `C_{k'}` is needed beyond
those on `C`. -/
noncomputable def picEt_baseChangeField_crossBaseIso_of_relPresheaf
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] (k' : Type u) [Field k']
    [Algebra k k']
    (e : PicSharp.relPresheaf (baseChangeField C k')
      ≅ (restrictTest k k').op ⋙ PicSharp.relPresheaf C) :
    picEt (baseChangeField C k') ≅ (restrictTest k k').op ⋙ picEt C :=
  picEt_crossBaseIso_of_relPresheaf C (baseChangeField C k') e

/-! ## §6. The cross-base identification, UNCONDITIONALLY -/

/-- **THE CROSS-BASE IDENTIFICATION FOR `picEt`, with no hypotheses beyond the
curve's own.** `AJC.picrep.etale-rep.crossbase`, closed.

For a smooth proper curve `C` over `k` and any field extension `k'/k`,

```
picEt (C_{k'})  ≅  (restrictTest k k').op ⋙ picEt C
```

as functors on `(Sch/k')ᵒᵖ`: the étale-sheafified relative Picard functor of the
base-changed curve agrees with that of `C` evaluated on restricted tests.

This is the input the repaired descent route needs in order for the `k'`-scheme
it produces to represent `picEt` **of the base-changed curve** rather than
`picEt` of the `k`-curve restricted — the mismatch that no green build would
reveal.

Assembled from `relPresheafCrossBaseIso` (the presheaf face: total-space
cancellation, coset-relation transport both ways, additivity, naturality) through
`picEt_baseChangeField_crossBaseIso_of_relPresheaf` (the sheafification layer,
free from Mathlib's continuity-compatibility iso).

**Scope, stated precisely.** No hypothesis on `C(k)`, per `I-0491`; and no
separability or finiteness hypothesis on `k'/k` either — the argument never
needed one, because it is about pullback projections rather than about étale
covers. The descent step that consumes it does need `k'/k` finite separable, but
that is a constraint of the *Galois* input, not of this identification.

**What it does NOT do**: it closes no `sorry` in
`Picard/FGAPicRepresentability.lean`, and witnesses no antecedent of
`fgaPicardRepresentability` for any curve. It is **one input of four** to the
route's repair — the others being the descent test
(`Picard/EtaleFieldCover.lean`, landed), the Galois action and quotient (`G1`/`G2`,
gated on `AlgebraicJacobian.GaloisDescent.HasGaloisQuotient`), and, upstream of
all three, a section over separably closed fields which has no producer in this
project at all (`I-1135`). The module docstring above states the same count; if
these two ever disagree, the module docstring is the one kept current. -/
noncomputable def picEt_crossBaseIso (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] (k' : Type u) [Field k']
    [Algebra k k'] :
    picEt (baseChangeField C k') ≅ (restrictTest k k').op ⋙ picEt C :=
  picEt_baseChangeField_crossBaseIso_of_relPresheaf C k'
    (relPresheafCrossBaseIso C k')

/-- The group-valued form: the étale Picard **sheaf** of the base-changed curve
agrees with the restriction of that of `C`. Same content as `picEt_crossBaseIso`
before forgetting the group structure. -/
noncomputable def etaleSheaf_crossBaseIso (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] (k' : Type u) [Field k']
    [Algebra k k'] :
    (PicSharp.etaleSheaf (baseChangeField C k')).obj
      ≅ (restrictTest k k').op ⋙ (PicSharp.etaleSheaf C).obj :=
  etaleSheaf_crossBaseIso_of_relPresheaf C (baseChangeField C k')
    (relPresheafCrossBaseIso C k')

end PicScheme

end Scheme

end AlgebraicGeometry
