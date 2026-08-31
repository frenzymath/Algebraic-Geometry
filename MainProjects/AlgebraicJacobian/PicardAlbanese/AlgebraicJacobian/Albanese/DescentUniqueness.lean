/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Albanese.BaseFieldFaithful
import AlgebraicJacobian.Picard.JacobianDataBaseChange
import AlgebraicJacobian.Picard.JacobianDataAbel

/-!
# S10 at the datum level: the Albanese uniqueness clause descends from `k̄` to `k`

`Albanese/BaseFieldFaithful.lean` proves that base change along an arbitrary field
extension is a faithful functor on `Over (Spec k)`.  This file spends that on the
Wave-6 descent leaf, at the interface the frozen gate actually consumes: the Jacobian
datum `d : JacobianData C` and its transport `d.baseChange L`.

The point of contact is a definitional one.  `JacobianData.baseChange`
(`Picard/JacobianDataBaseChange.lean:60`) is *defined* with representing object

```
(d.baseChange L).J = (AlgebraicGeometry.baseChange k L).obj d.J
```

so a morphism out of the base-changed Jacobian **is** a morphism out of the base change
of `d.J`, with no comparison isomorphism in between.  Faithfulness therefore applies on
the nose, and the uniqueness clause of `exists_unique_ofCurve_comp` over `k` follows from
the same clause over `L`.

## What this buys, and what it does not

The recon (`informal/w6-albanese-port-recon.md` §3, row S10) budgeted the whole leaf as
"finite-level spreading + Milne-6.4 uniqueness-first Galois argument + the
`(Jacobian C)_{k̄} ≅` representing-object comparison", with "nothing" landed or portable.
Two of those three items are not needed for uniqueness:

* **no finite-level spreading out** — faithfulness holds at `k → k̄` directly, since it
  needs only flatness and surjectivity of `Spec k̄ ⟶ Spec k`, neither of which sees
  finiteness.  §4.2's worry that the staging "at the *non-finite* extension k̄ is pinned
  nowhere" dissolves: there is nothing to stage;
* **no representing-object comparison, *for the transported datum*** —
  `(d.baseChange L).J` is the base change of `d.J` by definition, so `uniqueUpToIso` is
  not in the path.  Read this narrowly: if the `L`-side uniqueness is instead proved for
  an independently produced datum `dL : JacobianData C_L` — which is how the geometry
  over `k̄` would actually be available — then the comparison **is** needed.  §"The
  general case" below does that explicitly.  It costs `uniqueUpToIso` plus two rewrites
  (`subsingleton_hom_of_iso`), so it is not a new mathematical obligation; but it is
  present, and the narrow claim should not be quoted as the general one.

What remains genuinely Galois is **existence**: producing a `k`-morphism `d.J ⟶ A` from
a `k̄`-morphism.  Nothing here addresses it.

## Main declarations

* `AlgebraicGeometry.JacobianData.subsingleton_hom_baseChange_descends` — uniqueness of
  morphisms out of the base-changed Jacobian descends to uniqueness over `k`.
* `AlgebraicGeometry.JacobianData.existsUnique_ofCurve_comp_of_baseChange` — **the S10
  uniqueness half**: given the factorisation over `k` and uniqueness over `L`, the
  Albanese `∃!` holds over `k`.
* `AlgebraicGeometry.JacobianData.eq_of_baseChange_eq` — the raw descent of an equation
  between two morphisms out of the Jacobian.
* `AlgebraicGeometry.JacobianData.subsingleton_hom_of_iso` /
  `existsUnique_ofCurve_comp_of_baseChange_datum` — the same conclusion when the `L`-side
  uniqueness is proved for an **arbitrary** datum `dL` on `C_L` rather than the transport
  of `d`.  This one does route through `uniqueUpToIso`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

namespace JacobianData

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
  (L : Type u) [Field L] [Algebra k L]

/-- **Descent of an equation between morphisms out of the Jacobian.**  Two `k`-morphisms
`d.J ⟶ A` that agree after base change to `L` are equal.

The `L`-side equation is literally an equation of morphisms
`(d.baseChange L).J ⟶ (baseChange k L).obj A`, because `(d.baseChange L).J` is defined as
`(baseChange k L).obj d.J`; no transport is involved. -/
theorem eq_of_baseChange_eq (d : JacobianData C) {A : Over (Spec (.of k))}
    {g g' : d.J ⟶ A}
    (h : (AlgebraicGeometry.baseChange k L).map g
      = (AlgebraicGeometry.baseChange k L).map g') :
    g = g' :=
  eq_of_baseChange_map_eq (L := L) h

/-- **Uniqueness descends.**  If the base-changed Jacobian has at most one morphism to
`A_L`, then `d.J` has at most one morphism to `A`.

This is the shape Milne's uniqueness-first pattern needs: run the geometric argument
over `k̄`, where the symmetric-power and birationality machinery lives, and read the
conclusion off over `k`. -/
theorem subsingleton_hom_baseChange_descends (d : JacobianData C) {A : Over (Spec (.of k))}
    (h : Subsingleton ((d.baseChange L).J ⟶ (AlgebraicGeometry.baseChange k L).obj A)) :
    Subsingleton (d.J ⟶ A) :=
  subsingleton_of_subsingleton_baseChange (L := L) h

/-- **The S10 uniqueness half of the Albanese universal property.**

Assembles the frozen `∃!` over `k` from:

* `hex` — existence of *some* factorisation over `k`.  This is the Galois-cocycle half
  and is supplied by the caller; it is not proved here;
* `hL` — uniqueness of morphisms out of the base-changed Jacobian, i.e. the geometric
  argument run over `L = k̄`.

No Galois group, no cocycle, no spreading out to a finite level appears in the proof:
the descent is `Over.pullback`-faithfulness of a flat surjective base, which is
insensitive to whether `k → L` is finite, separable, or algebraic. -/
theorem existsUnique_ofCurve_comp_of_baseChange (d : JacobianData C)
    (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) {A : Over (Spec (.of k))} (f : C ⟶ A)
    (hex : ∃ g : d.J ⟶ A, f = d.ofCurve P ≫ g)
    (hL : Subsingleton ((d.baseChange L).J ⟶ (AlgebraicGeometry.baseChange k L).obj A)) :
    ∃! g : d.J ⟶ A, f = d.ofCurve P ≫ g := by
  obtain ⟨g, hg⟩ := hex
  exact ⟨g, hg, fun _ _ => (subsingleton_hom_baseChange_descends L d hL).elim _ _⟩

/-! ## The general case: uniqueness proved for an *independently produced* datum over `L`

The lemmas above take the `L`-side uniqueness at `(d.baseChange L).J`, the transport of
`d`.  But the way the geometry is actually available is different: over `k̄` one produces
a datum `dL : JacobianData C_L` in its own right (that is where the symmetric-power and
birationality machinery lives), and there is no reason for `dL` to be `d.baseChange L` on
the nose.

This is exactly the place where a representing-object comparison *is* needed — so the
claim "S10 needs no comparison" must be read narrowly: it holds for the transported
datum, not for an arbitrary one.  The comparison is cheap, though, and it is already
landed: `JacobianData.uniqueUpToIso` is an isomorphism of representing objects, and
transporting a `Subsingleton` of a `Hom`-set along an isomorphism of its source costs
two rewrites.  So the general case is not a new mathematical obligation, only one more
step. -/

/-- `Subsingleton` of a `Hom`-set transports along an isomorphism of the source. -/
theorem subsingleton_hom_of_iso {D : Type*} [Category D] {X X' Y : D} (e : X ≅ X')
    (h : Subsingleton (X' ⟶ Y)) : Subsingleton (X ⟶ Y) :=
  ⟨fun f g => by
    have hh : e.inv ≫ f = e.inv ≫ g := h.elim _ _
    have := congrArg (fun t => e.hom ≫ t) hh
    simpa using this⟩

/-- **The S10 uniqueness half, for uniqueness proved at an arbitrary `L`-datum.**

`dL : JacobianData C_L` is any datum on the base-changed curve — in particular one
produced over `k̄` by the geometry, with no relation to `d` assumed.  Uniqueness at
`dL.J` transports to `(d.baseChange L).J` through `uniqueUpToIso` (both represent
`Pic⁰_{C_L/L}`, so they are canonically isomorphic), and thence down to `k` by
faithfulness.

Together with `existsUnique_ofCurve_comp_of_baseChange` this covers both stagings, and
records honestly that the comparison is unavoidable in this one — cheap, but present. -/
theorem existsUnique_ofCurve_comp_of_baseChange_datum (d : JacobianData C)
    (dL : JacobianData ((AlgebraicGeometry.baseChange k L).obj C))
    (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) {A : Over (Spec (.of k))} (f : C ⟶ A)
    (hex : ∃ g : d.J ⟶ A, f = d.ofCurve P ≫ g)
    (hL : Subsingleton (dL.J ⟶ (AlgebraicGeometry.baseChange k L).obj A)) :
    ∃! g : d.J ⟶ A, f = d.ofCurve P ≫ g :=
  existsUnique_ofCurve_comp_of_baseChange L d P f hex
    (subsingleton_hom_of_iso ((d.baseChange L).uniqueUpToIso dL) hL)

end JacobianData

end AlgebraicGeometry
