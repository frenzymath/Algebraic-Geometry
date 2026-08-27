/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Genus
import AlgebraicJacobian.Picard.Pic0AbelianVariety
import AlgebraicJacobian.Albanese.CodimOneExtension

/-!
# The Albanese universal property of `Pic⁰_{C/k}`

This file states Milne's
*Abelian Varieties* §III.6 Proposition 6.1: for a complete nonsingular curve
`C` of genus `g > 0` over an algebraically closed field `k̄` and a marked
`k̄`-point `P₀ ∈ C(k̄)`, the Abel–Jacobi morphism
`ι_{P₀} : C ⟶ Pic⁰_{C/k̄}` is the **Albanese morphism** of the pointed curve
`(C, P₀)`: any pointed morphism `φ : C ⟶ A` into an abelian variety with
`φ(P₀) = η_A` factors uniquely as `φ = ψ ∘ ι_{P₀}` for a homomorphism of
group schemes `ψ : Pic⁰_{C/k̄} ⟶ A`.

The route taken is the **symmetric-power route** (cube-free): the
symmetric assignment `(P₁,…,P_g) ↦ φ(P₁) + ⋯ + φ(P_g)` factors through
`Sym^g C`, the resulting morphism `Sym^g φ : Sym^g C ⟶ A` descends through
the birational morphism `f^{(g)} : Sym^g C ⟶ Pic⁰_{C/k̄}` to a rational map
`Pic⁰_{C/k̄} ⇢ A`, and Milne's Theorem I.3.2 (`extend_to_av` in the sibling
`Albanese/Thm32RationalMapExtension.lean`, A.4.c) promotes it to a regular
morphism `ψ : Pic⁰_{C/k̄} ⟶ A`. The group-homomorphism property of `ψ` then
follows from `ψ(η_J) = η_A` together with Milne Corollary I.1.2 (a
consequence of `thm:rigidity_lemma`).

## Main results

* `Pic0.abelJacobi` — the regular morphism `ι_{P₀} : C ⟶ Pic⁰_{C/k̄}`
  (`lem:abel_jacobi_morphism`).
* `Pic0.SymmetricPower` — the `g`-th symmetric power `Sym^g C` of the curve
  `C`, as a `k̄`-scheme (Milne III.3 Proposition 3.1).
* `Pic0.symmetricPowerAVMap` — the symmetrised morphism
  `Sym^g φ : Sym^g C ⟶ A` induced by a morphism `φ : C ⟶ A` into an abelian
  variety.
* `Pic0.symmetricPowerToJacobian` — the birational morphism
  `f^{(g)} : Sym^g C ⟶ Pic⁰_{C/k̄}`.
* `Pic0.descentThroughBirationalSigma` — the descent of `Sym^g φ` to a unique
  regular morphism `ψ : Pic⁰_{C/k̄} ⟶ A`, via Milne Theorem I.3.2.
* `Pic0.albanese_eq_iff_symmetricPower_eq` — the connecting biconditional:
  `φ = ι_{P₀} ≫ ψ` holds iff `Sym^g φ = f^{(g)} ≫ ψ`.
* `Pic0.albanese_universal_property` — the universal property itself (Milne
  Proposition III.6.1), assembled from the previous two.

## Remaining obligations

**Status, measured (run 0069).** `albanese_universal_property` is *assembled*
from `descentThroughBirationalSigma` and `albanese_eq_iff_symmetricPower_eq`,
and that assembly is honest — but the headline is **not** sorry-free:
`#print axioms albanese_universal_property` reports `sorryAx`, inherited from
the six unproved declarations below. It should not be described as a landed
theorem until they close.

### Read this first: the mathematics is proved *elsewhere in this directory*

**Four of the six** obligations below are stated against `SymmetricPower`, which is a
`sorry`-**bodied definition**. An equation between morphisms out of a junk term
carries no information, so those four cannot be discharged, and discharging them
would establish nothing. They are kept because they pin the challenge's intended
statement shape, not because they are the work.

**Read the split, because this paragraph used to hide it** (corrected 2026-07-29; the
sentence above said "the six", and two of the three "active" roadmap rows repeat the
error — filed as inbox `I-0809`). The six divide into two groups with *different*
blockers, and only the first is about the symmetric power:

* `SymmetricPower`, `symmetricPowerAVMap`, `symmetricPowerToJacobian`,
  `albanese_eq_iff_symmetricPower_eq` — blocked on the symmetric power, and the reading
  "one missing object, not six gaps" is right about them.
* `descentThroughBirationalSigma` — also mentions `SymmetricPower`, but its *own* residue
  is the birationality data, which the symmetric power alone would not supply.
* `abelJacobi` — **does not mention `SymmetricPower` at all.** Its type is
  `C ⟶ jacobianScheme C`. Its blocker is the *Picard* seam: the moduli interpretation of
  `Pic⁰` applied to the rigidified diagonal correspondence, plus Yoneda. Nothing in
  `Albanese/` is a counterpart to it, so no amount of symmetric-power work discharges it,
  and the leg's headline needs it because the statement `φ = abelJacobi C P₀ ≫ ψ` is about
  it.

So "one missing object" is a fair summary of five sixths of this file and **not** of
`abelJacobi`.

Milne's argument itself **is** proved, over the symmetric power taken as an
*interface* rather than a `sorry`:

* `Albanese/SymPowInterface.lean` — `SymPowData C n` (carrier, symmetrisation
  projection, universal property), and everything Milne derives from it:
  `SymPowData.symAVMap` (his `Sym^n φ`, now a **construction**),
  `MonObj.basePointShift_comp_powSum` (the collapse behind "use `φ(P₀) = η_A`"),
  and `symPowDataOne` — which **inhabits** the interface (`Sym^1 C = C`), so
  statements quantifying over it are not vacuous.
* `Albanese/AlbaneseFromData.lean` — the connector in **both** directions and the
  universal property assembled over the interface. Worth knowing: the backward
  direction needs neither the quotient property nor that `ψ` is a homomorphism;
  only the forward direction does.
* `Albanese/AVSelfProduct.lean` — commutativity of an abelian variety and pointed
  rigidity, on the project's four-instance package.
* `Albanese/AlbaneseJacobian.lean` — the instantiation at `Pic⁰_{C/k̄}`, plus a
  machine check attributing its `sorryAx` entirely to the Picard seam: the same
  theorem with an arbitrary abelian variety target is axiom-clean.

So the honest description of the *symmetric-power part* of this leg is **one missing
object**: `SymPowData C g` for `g ≥ 2`. It is **not** the honest description of the leg,
and this sentence used to say it was: `abelJacobi` sits outside that object's reach (see
the split above) and is on the Picard seam.

**Update (2026-07-28) — that object is now identified, and the missing part is smaller than
this paragraph used to say.** `Albanese/SymPowColimit.lean` proves that `SymPowData C n`
*together with* its symmetry hypothesis **is** a colimit of the `S_n`-action on `C^n`, in
both directions (`hasColimit_permDiagram_iff`), so:

* the symmetry half is `colimit.w` — free, at every `n`;
* the **affine algebra** case is *inhabited* at every `n` (`symPowData_affineAlgebra`, in
  `(Under k)ᵒᵖ`), with no construction written. Identifying the carrier as
  `Spec (A^{⊗ n})^{S_g}` is expected but **not proved** — see that file's §5 header;
* what remains is the **gluing**, as one instance: `HasColimit (permDiagram C g)` — the
  colimit of the `S_g`-action on `C^g`, for this curve and this `g`. Do **not** state the
  residue as `HasColimitsOfShape (SingleObj (Equiv.Perm (Fin g))) Scheme`: that quantified
  form is strictly stronger, is not what `hasColimit_permDiagram_iff` covers, and is
  believed false at this pin, so a theorem carrying it would be vacuous.

The `analogies/m3-route-audit.md` figure of 2400–3800 lines priced the affine-and-glue
route as a whole (action typeclass, affine quotient with its universal property, glued
global quotient, smoothness). The first two are cheaper than that figure implies — the
affine-algebra quotient and its universal property come from mathlib's colimits — though
identifying the carrier and gluing remain. Treat the figure as historical and read
`Albanese/SymPowColimit.lean` before budgeting from it.

What *has* landed, and is genuinely unconditional, is the rational-map
extension this file consumes: `Scheme.RationalMap.extend_to_av` (Milne Theorem
3.2) is proved and axiom-clean as of run 0069, Milne Lemma 3.3 with it. So
`descentThroughBirationalSigma`'s *extension* step has a real input; what it
still lacks is the birationality data to build the rational map in the first
place (mathlib at this pin has no "invert a birational morphism on a dense
open" API).

The six declarations stated without proof:

* `abelJacobi` — the moduli classifier of the rigidified diagonal
  correspondence `𝓛^{P₀} = 𝓞_{C × C}(Δ − {P₀} × C − C × {P₀})`, taken as a
  relative degree-zero line bundle over the second factor.
* `SymmetricPower` — the affine-and-glue construction `Spec(A^{⊗ g})^{S_g}`
  of Milne III.3 Proposition 3.1 (Mumford 1970 §II.7 / §III.11). Mathlib has
  no scheme-theoretic symmetric power, only `Sym` for types and modules.
* `symmetricPowerAVMap` and `symmetricPowerToJacobian` — the two invocations
  of the universal property of `Sym^g C`, which need the symmetric projection
  `π : C^g ⟶ Sym^g C` supplied by that construction. Their *symmetric input* is
  proved (`MonObj.powSum` / `MonObj.powSum_perm`, `Albanese/GrpObjFoldSum.lean`);
  only the factorisation through `π` is missing.
* `descentThroughBirationalSigma` — extension of the rational map
  `Sym^g φ ∘ (f^{(g)})^{-1}` to a regular morphism (Milne Theorem I.3.2). The
  extension theorem `extend_to_av` is now proved and unconditional; the gap is
  upstream of it — producing the rational map, which needs the dense open on
  which `f^{(g)}` is an isomorphism *and* a way to invert it there.
* `albanese_eq_iff_symmetricPower_eq` — Milne's identification of `ι_{P₀}`
  with `Q ↦ Q + (g − 1) P₀` followed by `f^{(g)}`.

## The scheme `Pic⁰_{C/k̄}`

`Pic⁰_{C/k̄}` is taken from `Picard/Pic0AbelianVariety.lean` through a thin
`Pic0.Bundle` structure that carries the underlying scheme together with its
four abelian-variety attributes (`GrpObj`, `IsProper`, `Smooth`,
`GeometricallyIrreducible`), the carrier `Pic0.bundle C`, and the derived
definition `Pic0.jacobianScheme C := (bundle C).scheme`.

The upstream declarations `Scheme.Pic0.{grpObj, proper, smooth,
geometricallyIrreducible}` run under `[GeometricallyIntegral C.hom]`,
`[HasPicScheme C]` and `[PicScheme.PicSchemeLocallyOfFiniteType C]`, whereas
the Albanese curve enters carrying only smoothness, properness and geometric
irreducibility over `k̄`. The three bridges of §0.0
(`geometricallyReduced_of_smooth`, `GeometricallyIntegral.of_…`,
`hasRationalPoint_of_isAlgClosed`) discharge the missing hypotheses over an
algebraically closed base.

## Abelian-variety conventions

Following the project (cf. `AbelianVarietyRigidity.lean`, `Jacobian.lean`),
an **abelian variety over `k̄`** is encoded as an object
`A : Over (Spec (.of k̄))` carrying the four instances:

- `[GrpObj A]` (group-object structure on the over-category),
- `[IsProper A.hom]` (complete),
- `[Smooth A.hom]` (nonsingular),
- `[GeometricallyIrreducible A.hom]` (geometrically irreducible).

A **smooth proper geometrically irreducible curve over `k̄`** carries:

- `[SmoothOfRelativeDimension 1 C.hom]`,
- `[IsProper C.hom]`,
- `[GeometricallyIrreducible C.hom]`.

These instances are supplied by `inferInstance` at the call site.

## References

Blueprint: `blueprint/src/chapters/Albanese_AlbaneseUP.tex`.
Milne, *Abelian Varieties*, §III.6 Proposition 6.1, p. 104;
§III.3 Proposition 3.1 (symmetric power), p. 94; §III.5 Theorem 5.1(a)
(birationality of `f^{(g)}`), p. 101 (`references/abelian-varieties.pdf`).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

/-! ## §0.0. Substrate bridges: geometric integrality and rational points

`Picard/Pic0AbelianVariety.lean` states `Pic⁰_{C/k}` smooth,
proper and geometrically irreducible under the hypotheses
`[GeometricallyIntegral C.hom] [HasPicScheme C]
[PicScheme.PicSchemeLocallyOfFiniteType C]`, whereas the Albanese curve `C`
enters here carrying only `[SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
[GeometricallyIrreducible C.hom]` over an algebraically closed field `k̄`. The
three bridging facts below discharge the missing hypotheses, so that
`Pic0.bundle` can be assembled from the upstream declarations. -/

/-- **Reducedness descends along a faithfully flat morphism.** If `π : Y ⟶ X` is
flat and surjective (i.e. faithfully flat) and `Y` is reduced, then `X` is
reduced: each stalk map `𝒪_{X,π(y)} → 𝒪_{Y,y}` is a flat local homomorphism of
local rings, hence faithfully flat and in particular injective, so `𝒪_{X,π(y)}`
embeds into the reduced ring `𝒪_{Y,y}`. -/
theorem isReduced_of_flat_of_surjective {X Y : Scheme.{u}} (π : Y ⟶ X)
    [Flat π] [Surjective π] [IsReduced Y] : IsReduced X := by
  haveI hst : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := by
    intro x
    obtain ⟨y, rfl⟩ := π.surjective x
    have hlocal : IsLocalHom (π.stalkMap y).hom := inferInstance
    have hflat : (π.stalkMap y).hom.Flat := Flat.stalkMap π y
    have hinj : Function.Injective (π.stalkMap y).hom := by
      algebraize [(π.stalkMap y).hom]
      haveI : Module.Flat (X.presheaf.stalk (π.base y)) (Y.presheaf.stalk y) := hflat
      haveI : IsLocalHom (algebraMap (X.presheaf.stalk (π.base y)) (Y.presheaf.stalk y)) := hlocal
      haveI : Module.FaithfullyFlat (X.presheaf.stalk (π.base y)) (Y.presheaf.stalk y) :=
        Module.FaithfullyFlat.of_flat_of_isLocalHom
      exact FaithfulSMul.algebraMap_injective _ _
    exact isReduced_of_injective (π.stalkMap y).hom hinj
  exact isReduced_of_isReduced_stalk X

/-- **A scheme smooth over an algebraically closed field is geometrically
reduced.** For each test field `K/k̄`, the base change `X ×_{k̄} K` is smooth
over `K`; its further base change to `K̄ = AlgebraicClosure K` is smooth over an
algebraically closed field, hence reduced
(`Scheme.isReduced_of_smooth_of_isAlgClosed`), and reducedness descends along the
faithfully flat projection `X_{K̄} → X_K` (`isReduced_of_flat_of_surjective`). -/
theorem geometricallyReduced_of_smooth {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of kbar)) [Smooth f] :
    GeometricallyReduced f := by
  refine ⟨?_⟩
  rw [geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro K _ _
  have hfsurj : (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))).hom.FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  have hFS := (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))).mpr hfsurj
  haveI : Flat (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) := hFS.1
  haveI : Surjective (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) := hFS.2
  haveI hsm1 : Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap kbar K)))) :=
    inferInstance
  haveI hsm2 : Smooth (pullback.snd
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap kbar K))))
      (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))) := inferInstance
  haveI : Smooth (Over.mk (pullback.snd
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap kbar K))))
      (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))))).hom := hsm2
  haveI : IsReduced (pullback (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap kbar K))))
      (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))) :=
    Scheme.isReduced_of_smooth_of_isAlgClosed (kbar := AlgebraicClosure K) (Over.mk (pullback.snd
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap kbar K))))
      (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))))
  exact isReduced_of_flat_of_surjective
    (pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap kbar K))))
      (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))))

/-- **A smooth, geometrically irreducible curve over an algebraically closed
field has a rational point.** `C.left` is nonempty (geometric irreducibility over
the one-point base `Spec k̄`), locally of finite type over `k̄` (smoothness) and
therefore a Jacobson space, so it has a closed point `x`; over the algebraically
closed field `k̄`, `pointOfClosedPoint`/`pointEquivClosedPoint` promote `x` to a
`k̄`-rational section of `C.hom`. This discharges `[HasRationalPoint C]`. -/
theorem hasRationalPoint_of_isAlgClosed {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    (C : Over (Spec (.of kbar))) [Smooth C.hom] [GeometricallyIrreducible C.hom] :
    Scheme.HasRationalPoint C := by
  haveI : LocallyOfFiniteType C.hom := inferInstance
  haveI : IrreducibleSpace C.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton C.hom
  haveI : JacobsonSpace C.left := LocallyOfFiniteType.jacobsonSpace C.hom
  obtain ⟨x, hx⟩ := nonempty_inter_closedPoints (X := C.left) (Z := Set.univ)
    Set.univ_nonempty isClosed_univ.isLocallyClosed
  exact ⟨⟨(pointEquivClosedPoint C.hom).symm ⟨x, hx.2⟩⟩⟩

namespace Pic0

/-! ## §0. File-internal placeholder for `Pic⁰_{C/k̄}`

The identity component of the Picard scheme, together with its degree map, is
constructed in `Picard/Pic0AbelianVariety.lean`. The helper below — a bundled
structure carrying the Pic⁰ scheme together with its four abelian-variety
instances, plus the carrier `bundle` — supplies the interface. `bundle` is
wired to the upstream declarations (`Scheme.Pic0Scheme`,
`Scheme.Pic0.{grpObj, proper, smooth, geometricallyIrreducible}`) through the
§0.0 bridges; the derived `jacobianScheme` def and the four typeclass carriers
below are projections from `bundle`. -/

/-- Interface for `Pic⁰_{C/k̄}`: bundles the underlying `k̄`-scheme together
with the four abelian-variety structural instances (group object, proper,
smooth, geometrically irreducible).

**`C` OCCURS IN NO FIELD OF THIS STRUCTURE — it is a parameter the fields never
mention** (`review-ajc`, 2026-07-30, kernel-measured). The five fields constrain
`scheme` to be *some* proper smooth geometrically irreducible group object over
`k̄`, i.e. an abelian variety; nothing in the type ties it to the curve `C`.
Measured: for curves `C` and `D` with no relation whatever, `D`'s data inhabits
`Bundle C` — the anonymous-constructor term built entirely from `bundle D`'s
projections typechecks at type `Bundle C` (`lake env lean` EXIT=0). This is the
`HasDivFunctor` shape (`I-0838`: a carrier advertised as being about an object
that does not occur in its statement), one hop above the Picard seam.

**What limits the damage, stated so this is not read as worse than it is.**
`Bundle` is never *bound as a hypothesis*: the only term of this type in the
project is the canonical `bundle C` below, which pins `scheme := Pic⁰_{C/k̄}`,
and `jacobianScheme C = Scheme.Pic0Scheme C` holds by `rfl` (measured, with the
producer's three gates in scope). So every current consumer really is about `C`,
by definitional unfolding rather than by anything the type records.

**The hazard is therefore for the next author, which is why it is labelled here
rather than repaired.** Any future declaration that takes `(b : Bundle C)` as an
argument — the shape the words "Interface for `Pic⁰_{C/k̄}`" invite — would be a
theorem about an arbitrary abelian variety while reading as a theorem about the
Jacobian of `C`, and `abelJacobi`/the Albanese universal property below are
stated against `jacobianScheme C`, so the gap would not show up as a type error.
If such a consumer is ever wanted, add a field pinning the moduli property (a
`RepresentableBy` for the degree-zero part of `picEt C`, or an iso to
`Scheme.Pic0Scheme C`) before writing it. -/
structure Bundle {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    (C : Over (Spec (.of kbar)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom] where
  /-- The underlying scheme `Pic⁰_{C/k̄}`. -/
  scheme : Over (Spec (.of kbar))
  /-- Group-object structure on `Pic⁰_{C/k̄}`. -/
  grpObj : GrpObj scheme
  /-- Properness of `Pic⁰_{C/k̄}` over `k̄`. -/
  proper : IsProper scheme.hom
  /-- Smoothness of `Pic⁰_{C/k̄}` over `k̄`. -/
  smooth : Smooth scheme.hom
  /-- Geometric irreducibility of `Pic⁰_{C/k̄}` over `k̄`. -/
  geomIrred : GeometricallyIrreducible scheme.hom

variable {kbar : Type u} [Field kbar] [IsAlgClosed kbar]

variable (C : Over (Spec (.of kbar)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom]

/-- **The `Pic⁰_{C/k̄}` bundle.** For a smooth
proper geometrically irreducible curve `C` over an algebraically closed field
`k̄`, the underlying scheme is `Scheme.Pic0Scheme C` and its four
abelian-variety attributes are the identity-component theorems of
`Picard/Pic0AbelianVariety.lean` (`Scheme.Pic0.{grpObj, proper, smooth,
geometricallyIrreducible}`).

The upstream declarations run under `[GeometricallyIntegral C.hom]`,
`[HasPicScheme C]` and `[PicScheme.PicSchemeLocallyOfFiniteType C]`; over `k̄`
these are discharged honestly here:
`geometricallyReduced_of_smooth` + `GeometricallyIrreducible C.hom` give
`GeometricallyIntegral C.hom`; `hasRationalPoint_of_isAlgClosed` gives
`[HasRationalPoint C]`, whence `Scheme.picSchemeOfHasRationalPoint` supplies
`[HasPicScheme C]` and `instPicSchemeLocallyOfFiniteType` the local-finiteness
carrier.

Note the shape of that middle step since the étale rewire of 2026-07-28: the
`picSharp`-shaped gate `HasPicScheme` no longer has an instance, so it is named
explicitly here rather than synthesized. That is deliberate — nothing may pick up a
rational-point hypothesis by synthesis — and it is why this `k̄` bundle is honest: over
an algebraically closed field the rational point is a theorem, so supplying the gate
costs nothing. Over a general field it would not be available, which is exactly the
distinction the rewire makes visible. -/
noncomputable def bundle : Bundle C := by
  haveI : Smooth C.hom := SmoothOfRelativeDimension.smooth 1 C.hom
  haveI : GeometricallyReduced C.hom := geometricallyReduced_of_smooth C.hom
  haveI : GeometricallyIntegral C.hom :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible C.hom
  haveI : Scheme.HasRationalPoint C := hasRationalPoint_of_isAlgClosed C
  haveI := Scheme.picSchemeOfHasRationalPoint C
  exact
    { scheme := Scheme.Pic0Scheme C
      grpObj := (Scheme.Pic0.grpObj C).some
      proper := Scheme.Pic0.proper C
      smooth := Scheme.Pic0.smooth C
      geomIrred := Scheme.Pic0.geometricallyIrreducible C }

/-- The underlying `k̄`-scheme `Pic⁰_{C/k̄}` of a smooth proper
geometrically irreducible curve `C` over an algebraically closed field
`k̄`. Read off from the `Bundle` interface. -/
noncomputable def jacobianScheme : Over (Spec (.of kbar)) := (bundle C).scheme

/-- Group-object structure on `Pic⁰_{C/k̄}`. Deliberately **not** an
`instance`: while `Pic⁰_{C/k̄}` still depends on unproved upstream
statements, making this an instance would let `sorryAx` propagate silently
through typeclass synthesis. Consumers thread it explicitly via
`letI := jacobianScheme_grpObj C`. -/
@[implicit_reducible]
noncomputable def jacobianScheme_grpObj : GrpObj (jacobianScheme C) :=
  (bundle C).grpObj

/-- (Deliberately not an `instance`; see `jacobianScheme_grpObj`.) -/
theorem jacobianScheme_isProper : IsProper (jacobianScheme C).hom :=
  (bundle C).proper

/-- (Deliberately not an `instance`; see `jacobianScheme_grpObj`.) -/
theorem jacobianScheme_smooth : Smooth (jacobianScheme C).hom :=
  (bundle C).smooth

/-- (Deliberately not an `instance`; see `jacobianScheme_grpObj`.) -/
theorem jacobianScheme_geomIrred :
    GeometricallyIrreducible (jacobianScheme C).hom :=
  (bundle C).geomIrred

/-! ## §1. The Abel–Jacobi morphism at a marked point

The first sub-lemma packages the construction and elementary regularity
of the Abel–Jacobi morphism `ι_{P₀} : C ⟶ Pic⁰_{C/k̄}` at the basepoint
`P₀ ∈ C(k̄)`. On `k̄`-points,
`ι_{P₀}(Q) = [𝓞_C(Q − P₀)] ∈ Pic⁰_{C/k̄}(k̄)`; at the basepoint
itself `ι_{P₀}(P₀) = η_J`.

The morphism is the moduli classifier of
the rigidified diagonal correspondence
`𝓛^{P₀} = 𝓞_{C × C}(Δ − {P₀} × C − C × {P₀})` on `C × C`, taken as a
relative degree-zero line bundle on `C × C` over the second factor.

Blueprint reference: `lem:abel_jacobi_morphism` (Milne, *Abelian
Varieties*, Proposition III.6.1 and Summary III.6.11). -/

/-- **The Abel–Jacobi morphism at the marked basepoint `P₀`.**

For a smooth proper geometrically irreducible curve `C` over an
algebraically closed field `k̄` and a marked `k̄`-point
`P₀ : 𝟙_ ⟶ C`, the **Abel–Jacobi morphism** is the unique regular
morphism `ι_{P₀} : C ⟶ Pic⁰_{C/k̄}` characterised on `T`-points by the
formula `(1 × ι_{P₀})^* 𝓜^{P₀} ≈ 𝓛^{P₀}`, where `𝓜^{P₀}` is the
Poincaré–Picard correspondence on `C × Pic⁰_{C/k̄}` and
`𝓛^{P₀} = 𝓞_{C × C}(Δ − {P₀} × C − C × {P₀})`.

**Not yet constructed.** The construction applies the moduli interpretation
of `Pic⁰_{C/k̄}` (`def:pic_scheme` together with its identity-component
refinement) to the relative degree-zero line bundle `𝓛^{P₀}` on
`C × C → C` along the second projection; Yoneda then produces the
unique classifying morphism `C ⟶ Pic⁰_{C/k̄}`. The basepoint
condition `P₀ ≫ abelJacobi C P₀ = η[Pic⁰_{C/k̄}]` (`lem:abel_jacobi_morphism`)
holds because the restriction of `𝓛^{P₀}` to `C × {P₀}` is the trivial
line bundle `𝓞_C(P₀ − P₀) ≅ 𝓞_C`, whose moduli class is `η_J`. -/
noncomputable def abelJacobi (P0 : 𝟙_ (Over (Spec (.of kbar))) ⟶ C) :
    C ⟶ jacobianScheme C :=
  sorry

/-! ## §2. The `g`-th symmetric power `Sym^g C`

The `g`-th symmetric power of `C` is the quotient of the `g`-fold
Cartesian power `C^g` by the natural permutation action of the
symmetric group `S_g`. Mathlib `b80f227` has no formalised symmetric
power of a scheme — only `Sym` / `SymmetricPower` for types and
modules — so the scheme-theoretic construction must be supplied
project-side, following Milne's recipe of §III.3 Proposition 3.1: on
each open affine `U = Spec A ⊆ C` form `Spec(A^{⊗ g})^{S_g}`, then glue
along the standard open-cover patching (Mumford 1970 §II.7 / §III.11).

The construction is a prerequisite for the bodies of
`symmetricPowerAVMap` and `symmetricPowerToJacobian`, which need the
symmetric projection `π : C^g ⟶ Sym^g C` and its universal property. The
declaration below records the target `Sym^g C : Over (Spec k̄)` only; the
affine-and-glue construction is not yet formalised.

Blueprint reference: `def:symmetric_power_curve` (Milne, *Abelian
Varieties*, §III.3, Proposition 3.1, p. 94). -/

/-- **The `g`-th symmetric power `Sym^g C`** of a complete nonsingular
curve `C` over an algebraically closed field `k̄`, as a `k̄`-scheme.

Milne III.3 Proposition 3.1 constructs `Sym^g C` as the quotient of
`C^g` by the natural permutation action of the symmetric group `S_g`:
on each open affine `U = Spec A ⊆ C`, form `Spec(A^{⊗ g})^{S_g}`, then
glue along the standard open-cover patching. The construction comes
equipped with a canonical finite surjective symmetric morphism
`π : C^g ⟶ Sym^g C` characterised by the universal property that
every `S_g`-symmetric morphism `C^g ⟶ T` factors uniquely through `π`.

This declaration records the target scheme `Sym^g C`; the projection `π` and
its universal property belong with the construction.

**Not yet constructed.** The body is the gluing-of-affines
`Spec(A^{⊗ g})^{S_g}` construction over an open affine cover of `C`.

The signature mentions `C` explicitly (not via the file's `variable`
block) so that the declaration's first explicit argument is the curve
`C`, matching the call sites `SymmetricPower C g`. -/
noncomputable def SymmetricPower
    (C : Over (Spec (.of kbar)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom]
    (_g : ℕ) : Over (Spec (.of kbar)) :=
  sorry

/-! ## §3. The morphism `Sym^g φ : Sym^g C ⟶ A`

The second sub-lemma is the elementary fact that the symmetric
assignment `(P₁,…,P_g) ↦ φ(P₁) + ⋯ + φ(P_g)` from `C^g` to `A`
descends through `π : C^g ⟶ Sym^g C`. The key point is that the
`g`-fold addition morphism `add_A : A^g ⟶ A` is itself `S_g`-symmetric
because the underlying group object `A` is commutative as a group
scheme; combined with the universal property of `Sym^g C`, this yields
the unique factorisation.

Blueprint reference: `lem:symmetric_product_av_map` (Milne's proof of
III.6.1, p. 104, "Clearly this is symmetric, and so it factors through
`C^{(g)}`"). -/

/-- **The symmetrised morphism `Sym^g φ : Sym^g C ⟶ A`.**

Let `φ : C ⟶ A` be a morphism into an abelian variety `A` over `k̄`.
The composition `add_A ∘ φ^{×g} : C^g ⟶ A^g ⟶ A` sending
`(P₁,…,P_g) ↦ φ(P₁) + ⋯ + φ(P_g)` is `S_g`-equivariant (where `S_g`
permutes the factors of `C^g` and acts trivially on `A`), because
addition in a commutative group object is order-independent. By the
universal property of `Sym^g C` (`def:symmetric_power_curve`) it
factors uniquely as `Sym^g φ ∘ π = add_A ∘ φ^{×g}`.

**Not yet constructed — but the symmetric input now exists.** The morphism
`add_A ∘ φ^{×g} : C^g ⟶ A` and its `S_g`-invariance are supplied, proved, by
`Albanese/GrpObjFoldSum.lean`:

* `CategoryTheory.MonObj.powSum g φ : ∏ᶜ (fun _ : Fin g => C) ⟶ A` is the
  `g`-fold sum `(P₁,…,P_g) ↦ φ(P₁) + ⋯ + φ(P_g)`;
* `CategoryTheory.MonObj.powSum_perm` is exactly the equivariance
  `permAut C σ ≫ powSum g φ = powSum g φ` — Milne's "clearly this is
  symmetric", which reduces to the commutativity of `A`'s group law.

So what is missing here is *only* the universal-property invocation, i.e. the
projection `π : C^g ⟶ Sym^g C` and its factorisation property from the
construction of `Sym^g C` — not the symmetry that licenses the factorisation.
See the file header for why that construction is a separate subproject. -/
noncomputable def symmetricPowerAVMap (g : ℕ)
    {A : Over (Spec (.of kbar))}
    [GrpObj A] [IsProper A.hom] [Smooth A.hom] [GeometricallyIrreducible A.hom]
    (_φ : C ⟶ A) :
    SymmetricPower C g ⟶ A :=
  sorry

/-! ## §4. The birational morphism `Sym^g C ⟶ Pic⁰_{C/k̄}`

The third sub-lemma is the birational identification of `Sym^g C` with
`Pic⁰_{C/k̄}`. After choosing the basepoint `P₀ ∈ C(k̄)`, the cycle
map `(P₁,…,P_g) ↦ [𝓞_C(P₁ + ⋯ + P_g − g P₀)]` defines a regular
morphism `f^{(g)} : Sym^g C ⟶ Pic⁰_{C/k̄}` which is birational by
Milne III Theorem 5.1(a) (the proof uses dimension count plus the
Riemann–Roch identification of the generic fibre as a single point on
a curve of genus `g`).

Blueprint reference: `lem:symmetric_product_to_jacobian` (Milne,
*Abelian Varieties*, Theorem III.5.1(a), p. 101). -/

/-- **The birational morphism `f^{(g)} : Sym^g C ⟶ Pic⁰_{C/k̄}`.**

Given a basepoint `P₀ : 𝟙_ ⟶ C`, the symmetrisation of the Abel–Jacobi
morphism `add_J ∘ ι_{P₀}^{×g} : C^g ⟶ J^g ⟶ J` descends through
`π : C^g ⟶ Sym^g C` to a regular morphism
`f^{(g)} : Sym^g C ⟶ Pic⁰_{C/k̄}` sending an effective divisor class
`[P₁ + ⋯ + P_g]` to `[𝓞_C(P₁ + ⋯ + P_g − g P₀)] ∈ Pic⁰_{C/k̄}(k̄)`.
By Milne III Theorem 5.1(a) this morphism is *birational*: it is
dominant with one-dimensional fibres, and its generic fibre is a single
`k̄`-point (the linear system `|D|` of a general degree-`g` divisor `D`
on a curve of genus `g` is `0`-dimensional by Riemann–Roch).

The birationality data (a dense open subset `U ⊆ Sym^g C` mapping
isomorphically onto a dense open `V ⊆ Pic⁰_{C/k̄}`) is what
`descentThroughBirationalSigma` consumes.

**Not yet constructed.** The body is the specialisation of
`symmetricPowerAVMap` to `A := jacobianScheme C` and
`φ := abelJacobi C P₀`. -/
noncomputable def symmetricPowerToJacobian
    (_P0 : 𝟙_ (Over (Spec (.of kbar))) ⟶ C) (g : ℕ) :
    SymmetricPower C g ⟶ jacobianScheme C :=
  sorry

/-! ## §5. Descent through the birational quotient

The final auxiliary lemma packages the two-step descent that promotes
`Sym^g φ : Sym^g C ⟶ A` (after passing through the birational morphism
`f^{(g)} : Sym^g C ⟶ Pic⁰_{C/k̄}`) to a regular morphism
`ψ : Pic⁰_{C/k̄} ⟶ A`. The descent is a rational map
`Pic⁰_{C/k̄} ⇢ A` on the dense open of `Pic⁰_{C/k̄}` on which
`f^{(g)}` is an isomorphism, then promoted to a regular morphism via
Milne's Theorem I.3.2 (the sibling `Albanese/Thm32RationalMapExtension.lean`).
This is the only step of the proof that uses the rational-map extension.

Blueprint reference: `lem:descent_through_birational_sigma` (Milne's
proof of III.6.1, p. 104, "It therefore defines a rational map
`ψ : J → A`, which (I 3.2) shows to be a regular map"). -/

/-- **Descent of `Sym^g φ` to a regular morphism `ψ : Pic⁰_{C/k̄} ⟶ A`.**

There is a *unique* regular morphism `ψ : Pic⁰_{C/k̄} ⟶ A` such that
`symmetricPowerAVMap C (genus C) φ = symmetricPowerToJacobian C P₀ (genus C) ≫ ψ`
(equivalently, `ψ` is the unique regular extension of the rational map
`Sym^g φ ∘ (f^{(g)})^{-1} : Pic⁰_{C/k̄} ⇢ A`).

The rational map is constructed on the dense open `V ⊆ Pic⁰_{C/k̄}`
where `f^{(g)}` is an isomorphism, then promoted to a regular morphism
on all of `Pic⁰_{C/k̄}` via Milne's Theorem I.3.2 (sibling
`Scheme.RationalMap.extend_to_av` in
`Albanese/Thm32RationalMapExtension.lean`). Uniqueness is the
standard reduced-and-separated agreement principle: two regular
morphisms `Pic⁰_{C/k̄} ⟶ A` agreeing on a dense open are equal.

**Not yet proved — but the extension half is done.** The gap is now precisely
one thing: the *birationality data*. Specifically:

* `Scheme.RationalMap.exists_unique_hom_restrict_eq_of_dense_open`
  (`Albanese/DenseOpenDescent.lean`) says that given **any** dense open
  `V ⊆ Pic⁰_{C/k̄}` and **any** morphism `h : V ⟶ A` compatible with the
  structure maps, there is a unique `ψ : Pic⁰_{C/k̄} ⟶ A` with `V.ι ≫ ψ = h`.
  It is proved and axiom-clean, resting on `extend_to_av` (Milne Theorem 3.2),
  itself unconditional since Milne Lemma 3.3 closed.

So no further extension, properness or agreement argument is needed here. What
remains is to *produce* `V` and `h`: the dense open of `Pic⁰_{C/k̄}` over which
`f^{(g)}` admits a section, and that section composed with `Sym^g φ`. That needs
(i) `Sym^g C` and `f^{(g)}` to exist at all, and (ii) Milne III Theorem 5.1(a)'s
birationality in a usable form — mathlib at this pin has no API for inverting a
birational morphism on a dense open (`Mathlib/AlgebraicGeometry/Birational/`
supplies `IsDominant`, not an inverse). -/
theorem descentThroughBirationalSigma
    (P0 : 𝟙_ (Over (Spec (.of kbar))) ⟶ C)
    {A : Over (Spec (.of kbar))}
    [GrpObj A] [IsProper A.hom] [Smooth A.hom] [GeometricallyIrreducible A.hom]
    (φ : C ⟶ A) (_hφ : P0 ≫ φ = η[A]) :
    ∃! (ψ : jacobianScheme C ⟶ A),
      symmetricPowerAVMap C (genus C) φ
        = symmetricPowerToJacobian C P0 (genus C) ≫ ψ := by
  sorry

/-! ## §5.5. Albanese ⇔ symmetric-power equation (connecting biconditional)

This section isolates the *connecting identity* between the Albanese-form
factorisation `φ = abelJacobi C P₀ ≫ ψ` and the symmetric-power-form
factorisation `symmetricPowerAVMap C (genus C) φ =
symmetricPowerToJacobian C P₀ (genus C) ≫ ψ`. Given that biconditional,
`albanese_universal_property` follows from
`descentThroughBirationalSigma` by pure assembly. -/

/-- **Connecting biconditional: Albanese-form equation ⇔ symmetric-power-form
equation.**

For every candidate descent morphism `ψ : Pic⁰_{C/k̄} ⟶ A`, the Albanese-form
factorisation `φ = abelJacobi C P₀ ≫ ψ` holds iff the symmetric-power-form
factorisation `symmetricPowerAVMap C (genus C) φ = symmetricPowerToJacobian
C P₀ (genus C) ≫ ψ` holds. The forward direction precomposes both sides of
the Albanese equation with the symmetric `g`-fold sum, then descends through
`π : C^g ⟶ Sym^g C` and uses the additivity of `ψ` (a homomorphism of group
schemes). The reverse direction restricts the symmetric-power-form equation
along the diagonal embedding `Q ↦ (Q, P₀, …, P₀)` and uses
`φ(P₀) = η_A`.

**Not yet proved.** The proof uses the `Sym^g` projection `π` and its
universal property, together with the Milne III §6 identification of
`ι_{P₀}` with the composite of `Q ↦ Q + (g − 1) P₀` followed by
`f^{(g)}`. -/
theorem albanese_eq_iff_symmetricPower_eq
    (P0 : 𝟙_ (Over (Spec (.of kbar))) ⟶ C)
    {A : Over (Spec (.of kbar))}
    [GrpObj A] [IsProper A.hom] [Smooth A.hom] [GeometricallyIrreducible A.hom]
    (φ : C ⟶ A) (_hφ : P0 ≫ φ = η[A]) :
    ∀ (ψ : jacobianScheme C ⟶ A),
      (φ = abelJacobi C P0 ≫ ψ) ↔
      (symmetricPowerAVMap C (genus C) φ
        = symmetricPowerToJacobian C P0 (genus C) ≫ ψ) :=
  sorry

/-! ## §6. The Albanese universal property — headline theorem

The headline result of the chapter: for every pointed morphism
`φ : C ⟶ A` into an abelian variety `A` with `φ(P₀) = η_A`, there
exists a unique regular morphism `ψ : Pic⁰_{C/k̄} ⟶ A` such that
`φ = ψ ∘ ι_{P₀}`. The proof follows Milne Proposition III.6.1
verbatim, using the four sub-lemmas above plus Milne Theorem I.3.2
(`extend_to_av`) and Corollary I.1.2 (a `thm:rigidity_lemma`
consequence).

Blueprint reference: `thm:albanese_universal_property` (Milne,
*Abelian Varieties*, Proposition III.6.1, p. 104). -/

/-- **Albanese universal property of `Pic⁰_{C/k̄}` — Milne III §6
Proposition 6.1.**

For a complete nonsingular curve `C` of genus `g > 0` over an
algebraically closed field `k̄`, a marked `k̄`-point `P₀ ∈ C(k̄)`, and
every pointed morphism `φ : C ⟶ A` into an abelian variety `A` with
`φ(P₀) = η_A`, there exists a *unique* regular morphism
`ψ : Pic⁰_{C/k̄} ⟶ A` such that `φ = ι_{P₀} ≫ ψ`.

Proof sketch (Milne III.6.1):
1. **Symmetrisation.** `(P₁,…,P_g) ↦ φ(P₁) + ⋯ + φ(P_g)` is
   `S_g`-symmetric (`A` commutative), so factors through
   `Sym^g C` as `Sym^g φ` (`lem:symmetric_product_av_map`).
2. **Descent to a regular morphism on `J`.** The birational morphism
   `f^{(g)} : Sym^g C ⟶ Pic⁰_{C/k̄}` (`lem:symmetric_product_to_jacobian`)
   exhibits `Sym^g φ ∘ (f^{(g)})^{-1}` as a rational map
   `Pic⁰_{C/k̄} ⇢ A`, which by Milne Theorem I.3.2 extends uniquely to
   a regular morphism `ψ : Pic⁰_{C/k̄} ⟶ A`
   (`lem:descent_through_birational_sigma`).
3. **Factorisation `ψ ∘ ι_{P₀} = φ`.** Use Milne's identification of
   `ι_{P₀}` with the composite `Q ↦ Q + (g − 1) P₀` followed by
   `f^{(g)}`; together with `φ(P₀) = η_A` and the additive structure
   of `A`, this gives `ψ(ι_{P₀}(Q)) = φ(Q)` on `k̄`-points, hence
   globally by the reduced-and-separated agreement principle.
4. **Homomorphism property.** `ψ` sends `η_J = ι_{P₀}(P₀)` to
   `φ(P₀) = η_A`, so by Milne Corollary I.1.2 (a `thm:rigidity_lemma`
   consequence) it is a homomorphism of group schemes.
5. **Uniqueness.** Two homomorphisms `Pic⁰_{C/k̄} ⟶ A` with the same
   restriction to `ι_{P₀}(C)` agree on the `g`-fold sum
   `ι_{P₀}(C) + ⋯ + ι_{P₀}(C) = Pic⁰_{C/k̄}` (since `f^{(g)}` is
   surjective), hence are equal.

The statement asserts only the existence and uniqueness of the factoring
morphism `ψ : Pic⁰_{C/k̄} ⟶ A` (matching the project's `IsAlbanese`
convention in `Jacobian.lean`); the group-homomorphism property is implicit
in the construction, by Milne Corollary I.1.2 (registered in
`chap:AbelianVarietyRigidity`).

The proof below is pure assembly: `descentThroughBirationalSigma` (§5)
transported across `albanese_eq_iff_symmetricPower_eq` (§5.5). Both of
those, and the constructions of §1–§4 they rest on, are still unproved —
see the file header.

**Therefore this theorem is NOT sorry-free**, and must not be reported as a
landed result. `#print axioms albanese_universal_property` reports
`[propext, sorryAx, Classical.choice, Quot.sound]` (measured, run 0069). The
assembly is honest and the statement is the right one; what is missing is
everything the statement quantifies over — in particular `abelJacobi`, whose
`sorry`-bodied *definition* means the equation `φ = abelJacobi C P₀ ≫ ψ` does
not yet say what it is meant to say. Step 4 (the homomorphism property, via
Milne Corollary I.1.2) does have a real input: the rigidity chain in
`RigidityLemma.lean` is sorry-free and axiom-clean. -/
theorem albanese_universal_property
    (_hg : 0 < genus C)
    (P0 : 𝟙_ (Over (Spec (.of kbar))) ⟶ C)
    {A : Over (Spec (.of kbar))}
    [GrpObj A] [IsProper A.hom] [Smooth A.hom] [GeometricallyIrreducible A.hom]
    (φ : C ⟶ A) (_hφ : P0 ≫ φ = η[A]) :
    ∃! (ψ : jacobianScheme C ⟶ A), φ = abelJacobi C P0 ≫ ψ := by
  -- Transport the symmetric-power descent `descentThroughBirationalSigma`
  -- across the connecting biconditional `albanese_eq_iff_symmetricPower_eq`.
  have key := albanese_eq_iff_symmetricPower_eq C P0 φ _hφ
  obtain ⟨ψ, hψ_sym, huniq_sym⟩ := descentThroughBirationalSigma C P0 φ _hφ
  exact ⟨ψ, (key ψ).mpr hψ_sym,
    fun ψ' hψ' => huniq_sym ψ' ((key ψ').mp hψ')⟩

end Pic0

end AlgebraicGeometry
