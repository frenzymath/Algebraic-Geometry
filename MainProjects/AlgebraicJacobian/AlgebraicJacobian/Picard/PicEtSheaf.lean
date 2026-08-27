/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Picard.RelPicFunctor

/-!
# The étale-sheafified relative Picard functor

This file constructs the **étale-sheafified relative Picard functor**
`Pic_{(C/k)ét}` of a smooth proper curve `C/k` and proves that it *is* a sheaf
for the étale topology — the object whose representability is the project's
central open obligation (`Picard/FGAPicRepresentability.lean`).

## Why the sheafification is the right object

The relative Picard presheaf `T ↦ Pic(C ×_k T)/π_T^* Pic(T)`
(`Scheme.PicSharp.relPresheaf`, Kleiman §2 Def. `df:Pfs`) is in general **not
a sheaf** (Kleiman §2, L1330: "not *a priori* a sheaf"), and over a general
field it is **not representable** — the witness is Exercise `ex:Pfs`, the conic
`u²+v²+w²=0` in `ℙ²_ℝ`, smooth proper geometrically integral with no rational
point.

**CITATION CORRECTED 2026-07-29 (`review-ajc`).** This paragraph asserted
non-sheafness "not even for the Zariski topology (Kleiman §2, L1292–L1302)",
and glossed it as: a line bundle can be trivial on each member of a cover of `T`
without being trivial modulo `π_T^* Pic(T)`. Both the citation and the gloss are
wrong. L1292–L1302 proves that the **absolute** functor `Pic_X` is never a
separated Zariski presheaf, using `T = ℙ¹_X`; the quotient by `π_T^* Pic(T)`
that defines the *relative* functor is exactly what kills that argument, and
L1600–L1605 in fact proves `Pic_{X/S} ≅ Pic_{(X/S)zar}` when `f` has a section.
Sheafifying is still the right move and the conclusion below is unaffected —
only the stated reason was. Full account in
`Picard/FGAPicRepresentability.lean`'s module docstring.

Kleiman's representability theorem (§4 Thm. `th:main`) is
therefore a statement about the associated **étale** sheaf, and it is that
statement which is true over an arbitrary base field with no rational-point
hypothesis.

There are two ways to reach a sheaf, and they differ in what has to be
supplied:

1. assume `C` has a `k`-rational point. Then Kleiman §2 Thm. 2.5 says the
   comparison `Pic_{C/k} → Pic_{(C/k)ét}` is already bijective, so the plain
   presheaf is the sheaf. This is *strictly weaker* than the challenge, whose
   curve need not have a rational point, and it is the route the conditional
   `Scheme.picSchemeOfHasRationalPoint` records;
2. sheafify. Nothing is assumed about `C(k)`, and the sheaf axiom holds by
   construction. This is the route realised here and the one the project
   claims (owner decision of 2026-07-28).

## The site

Mathlib `v4.31` carries the big étale site on schemes,
`AlgebraicGeometry.Scheme.etaleTopology = grothendieckTopology @Etale`
(`Mathlib/AlgebraicGeometry/Sites/Etale.lean`). The relative Picard presheaf
lives on the slice `Over (Spec k)` rather than on `Scheme`, so the topology is
transported along the localisation of SGA 4 III 5.2.1, available in Mathlib as
`GrothendieckTopology.over`: a sieve of `T : Over (Spec k)` covers iff the
corresponding sieve of `T.left` covers étale-locally. That transport is where
"the étale topology on `(Sch/k)`" becomes a definition rather than a parameter,
and it is what lets the sheaf property below be a *theorem* rather than a
hypothesis.

## Main definitions

* `Scheme.etaleTopologyOver k` — the étale topology on `(Sch/k) = Over (Spec k)`.
* `Scheme.PicSharp.etaleSheaf C` — `Pic_{(C/k)ét}`, a bundled
  `Sheaf (etaleTopologyOver k) AddCommGrpCat`, obtained by sheafifying the
  relative Picard presheaf.
* `Scheme.PicSharp.etaleSheaf_isSheaf` — the sheaf property, extracted as a
  standalone statement about the underlying presheaf.
* `Scheme.PicScheme.picEt C` — the set-valued functor
  `T ↦ Pic_{(C/k)ét}(T)` that the representability obligation is stated
  against, together with `picEtComparison C`, the canonical comparison
  `picSharp C ⟶ picEt C` from the unsheafified functor.
* `Scheme.PicScheme.picEt_isSheaf_forget` — the sheaf property of `picEt`
  itself (the group structure forgotten), which is what a representing scheme
  must match.

## References

Kleiman, "The Picard scheme" (arXiv:math/0504020), §2 Def. `df:Pfs` (the
étale-sheaf clause) and Thm. 2.5 (`th:comp`), §4 Thm. `th:main`.
Blueprint: `def:rel_pic_etale_sheafification`,
`thm:rel_pic_etale_sheaf_group_structure`, `sec:fga_pic_setup`.
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace Scheme

/-! ## §1. The étale site of `(Sch/k)` -/

/-- **The étale topology on `(Sch/k)`.**

The big étale topology on schemes (`Scheme.etaleTopology`, Mathlib
`AlgebraicGeometry/Sites/Etale.lean`) localised at `Spec k` along SGA 4
III 5.2.1 (`GrothendieckTopology.over`): a sieve of a `k`-scheme `T` is
covering exactly when the sieve it generates on the underlying scheme
`T.left` is covering for the étale topology
(`GrothendieckTopology.mem_over_iff`).

This is the site on which the relative Picard presheaf of
`Picard/RelPicFunctor.lean` lives, so it is the site whose sheafification
produces Kleiman's `Pic_{(C/k)ét}`. Note that the earlier
`PicSharp.etSheaf` of that file takes the topology as a *parameter*, for
want of a canonical choice; this definition supplies the canonical one, and
`PicSharp.etaleSheaf` below is the instantiation. -/
noncomputable abbrev etaleTopologyOver (k : Type u) [Field k] :
    GrothendieckTopology (Over (Spec (CommRingCat.of k))) :=
  Scheme.etaleTopology.over (Spec (CommRingCat.of k))

/-- The étale topology on `(Sch/k)` refines the Zariski one: a Zariski cover
of a `k`-scheme is an étale cover. Transported from
`zariskiTopology_le_etaleTopology` through the localisation, which is
monotone because `mem_over_iff` characterises membership by the pushed-forward
sieve on the underlying scheme.

Recorded because it is the precise sense in which sheafifying étale-locally is
*stronger* than sheafifying Zariski-locally: a Zariski sheaf need not be an
étale sheaf, and the relative Picard presheaf is not even the former. -/
theorem zariskiTopologyOver_le_etaleTopologyOver (k : Type u) [Field k] :
    (Scheme.zariskiTopology.over (Spec (CommRingCat.of k))) ≤ etaleTopologyOver k := by
  intro T S hS
  rw [GrothendieckTopology.mem_over_iff] at hS ⊢
  exact Scheme.zariskiTopology_le_etaleTopology _ hS

namespace PicSharp

/-! ## §2. The étale-sheafified relative Picard functor -/

/-- **The étale-sheafified relative Picard functor** `Pic_{(C/k)ét}`
(Kleiman §2 Def. `df:Pfs`, étale-sheaf clause).

The associated étale sheaf of the relative Picard presheaf
`T ↦ Pic(C ×_k T)/π_T^* Pic(T)` (`PicSharp.relPresheaf`), as a bundled object
of `Sheaf (etaleTopologyOver k) AddCommGrpCat`. Its sheaf property is not an
assumption but part of the datum — `Sheaf.cond`, extracted as
`etaleSheaf_isSheaf` below — which is the whole point of passing to it: the
unsheafified `relPresheaf` is not *a priori* an étale sheaf (Kleiman §2 L1330),
so representability of `Pic_{(C/k)ét}` is the statement one can ask for over an
arbitrary field.

**Corrected 2026-07-30 (`review-ajc`): this said "not a sheaf even
Zariski-locally", and that is the withdrawn claim.** It is wrong about exactly
the functor named here. The lines it derives from (Kleiman §2 L1292–L1302) prove
that the **absolute** `Pic_X` is never a separated Zariski presheaf; the
**relative** functor — `relPresheaf`, this one — is *defined* by quotienting out
`Pic(T)` precisely to defeat that argument. On these binders `th:cmp` part 1
gives the opposite direction *in Kleiman*, `Pic_{X/S} ↪ Pic_{(X/S)zar}` whenever
`O_S = f_*O_X` universally, i.e. `relPresheaf` is Zariski-**separated** there.

**That last clause is about the SOURCE, and the Lean name first cited here does
not carry it** (`review-ajc`, corrected in the same session by a fresh-context
audit of this very fix). `PicScheme.picSharp_isSheaf_zariski_of_representableBy`
(`Picard/PicEtSubcanonical.lean`) takes a `rep : (picSharp C).RepresentableBy X`
hypothesis and concludes the Zariski sheaf property *from representability*, by
subcanonicity — the converse direction, conditional on exactly what the seam
lacks. `PicEtSubcanonical`'s §4 docstring scopes it correctly as "only the first
half"; that caveat was dropped in copying the citation here. **Nothing in this
project proves `th:cmp` part 1.**

The seam and the blueprint were both corrected
for this on 2026-07-29 (`I-0970`, `I-0973`) and this site was missed. Do not
restore a Zariski-sheaf reason here; take the non-representability directly, via
`PicScheme.not_exists_representing_picSharp_of_not_isIso`, whose one open input is
that the comparison really fails for Kleiman's pointless real conic.

This is a genuine instantiation of the parametric `PicSharp.etSheaf` of
`Picard/RelPicFunctor.lean` at the canonical étale topology, with one
correction: `etSheaf` sheafifies the *absolute* functor `PicSharp.presheaf`
(`T ↦ Pic(C ×_k T)`), whereas Kleiman's `Pic_{(C/k)ét}` and the
representability theorem are about the *relative* one, `relPresheaf`. It is
the relative functor that is sheafified here.

The abelian-group structure survives sheafification because the target
`AddCommGrpCat` has the sheafification adjunction
(`HasWeakSheafify` for a concrete, filtered-colimit-preserving forgetful
functor); `toEtaleSheaf` below is the unit. -/
noncomputable def etaleSheaf {k : Type u} [Field k] (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] :
    Sheaf (etaleTopologyOver k) AddCommGrpCat.{u+1} :=
  (CategoryTheory.presheafToSheaf (etaleTopologyOver k) AddCommGrpCat.{u+1}).obj
    (PicSharp.relPresheaf C)

/-- **The sheaf property of `Pic_{(C/k)ét}`, as a standalone statement.**

The underlying presheaf of `PicSharp.etaleSheaf C` satisfies the sheaf axiom
for the étale topology on `(Sch/k)`. This is `Sheaf.cond` of the bundled
object, stated separately because it is the property consumers cite: a
representing scheme for `Pic_{(C/k)ét}` exists only because the functor being
represented is an étale sheaf (a representable functor is a sheaf for any
subcanonical topology, so a non-sheaf can never be representable — which is
exactly why the unsheafified `relPresheaf` needs a rational point).

Proved, not assumed: sheafification produces a sheaf. -/
theorem etaleSheaf_isSheaf {k : Type u} [Field k] (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] :
    Presheaf.IsSheaf (etaleTopologyOver k) (etaleSheaf C).obj :=
  (etaleSheaf C).property

/-- **The comparison map** `Pic_{C/k} ⟶ Pic_{(C/k)ét}`, i.e. the unit of the
sheafification adjunction at the relative Picard presheaf.

Kleiman §2 Thm. 2.5 (`th:comp`) says this map is an isomorphism when `C` has a
`k`-rational point (and `O_S = f_* O_X` universally, automatic here). Over an
arbitrary base field it is only a comparison: the honest object is the target,
which is why the representability obligation is stated there. -/
noncomputable def toEtaleSheaf {k : Type u} [Field k] (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] :
    PicSharp.relPresheaf C ⟶ (etaleSheaf C).obj :=
  CategoryTheory.toSheafify (etaleTopologyOver k) (PicSharp.relPresheaf C)

/-- The universal property of the sheafification, in the form consumers use:
every morphism from the relative Picard presheaf to (the underlying presheaf
of) an étale sheaf factors uniquely through `toEtaleSheaf`.

This is what makes `Pic_{(C/k)ét}` the *canonical* choice rather than one
sheaf among many, and it is the step that turns a representing scheme for the
sheaf into a universal receiver of relative Picard classes. -/
noncomputable def etaleSheafHomEquiv {k : Type u} [Field k]
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    (G : Sheaf (etaleTopologyOver k) AddCommGrpCat.{u + 1}) :
    (etaleSheaf C ⟶ G) ≃ (PicSharp.relPresheaf C ⟶ G.obj) :=
  ((CategoryTheory.sheafificationAdjunction (etaleTopologyOver k)
    AddCommGrpCat.{u + 1}).homEquiv (PicSharp.relPresheaf C) G)

end PicSharp

namespace PicScheme

/-! ## §3. The set-valued functor that gets represented -/

/-- **The functor whose representability is the project's central obligation**:
the étale-sheafified relative Picard functor with its group structure
forgotten,

```
picEt C : (Sch/k)^op ⥤ Type (u+1),   T ↦ Pic_{(C/k)ét}(T).
```

Representability is a statement about the underlying set-valued functor; the
group structure is transported back onto the representing scheme by Yoneda
(`PicScheme.groupSchemeStructure`), exactly as for the unsheafified
`picSharp`.

Contrast with `picSharp C = relPresheaf C ⋙ forget`: that functor is
representable only under a rational-point hypothesis (it is not even a
Zariski sheaf otherwise), whereas *this* one is the object of Kleiman §4
Thm. `th:main` and its representability needs no hypothesis on `C(k)`. -/
noncomputable def picEt {k : Type u} [Field k] (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] :
    (Over (Spec (CommRingCat.of k)))ᵒᵖ ⥤ Type (u+1) :=
  (PicSharp.etaleSheaf C).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u+1}

/-- The comparison `picSharp C ⟶ picEt C` of set-valued functors, the
set-level shadow of `PicSharp.toEtaleSheaf`. An isomorphism under a
`k`-rational point (Kleiman §2 Thm. 2.5), a comparison in general.

The source is written out as `PicSharp.relPresheaf C ⋙ forget _` rather than as
`picSharp C`, which is the *same functor by definition* but is declared in the
downstream `Picard/FGAPicRepresentability.lean` (that file imports this one, so
the name is not available here). -/
noncomputable def picEtComparison {k : Type u} [Field k]
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] :
    PicSharp.relPresheaf C ⋙ CategoryTheory.forget AddCommGrpCat.{u+1} ⟶ picEt C :=
  CategoryTheory.Functor.whiskerRight (PicSharp.toEtaleSheaf C)
    (CategoryTheory.forget AddCommGrpCat.{u+1})

/-- **`picEt` is an étale sheaf of sets.**

The sheaf property of `Pic_{(C/k)ét}` survives forgetting the group structure,
because the forgetful functor `AddCommGrpCat ⥤ Type` preserves the limits the
sheaf condition is stated by. Together with the fact that a representable
functor is a sheaf for a subcanonical topology, this is the structural reason
the representability obligation is *consistent* as stated — which the
unsheafified `picSharp` version was not, absent a rational point. -/
theorem picEt_isSheaf_forget {k : Type u} [Field k]
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] :
    Presieve.IsSheaf (etaleTopologyOver k) (picEt C) := by
  have h := ((CategoryTheory.sheafCompose (etaleTopologyOver k)
    (CategoryTheory.forget AddCommGrpCat.{u+1})).obj (PicSharp.etaleSheaf C)).property
  rw [CategoryTheory.isSheaf_iff_isSheaf_of_type] at h
  exact h

end PicScheme

end Scheme

end AlgebraicGeometry
