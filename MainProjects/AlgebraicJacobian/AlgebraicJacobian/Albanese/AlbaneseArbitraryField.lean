/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Albanese.AVRigidityArbitraryField
import AlgebraicJacobian.Albanese.AlbaneseJacobian
import AlgebraicJacobian.Albanese.SymPowColimit
import AlgebraicJacobian.Jacobian

/-!
# The Albanese universal property over an arbitrary base field

`Albanese/AlbaneseJacobian.lean` instantiates Milne Proposition III.6.1 over an
**algebraically closed** field. This file removes that restriction, and states the result
in the shape the headline's fifth obligation `isAlbanese_pic0Et` (`Jacobian.lean`) asks
for: `IsAlbanese C P J`, over an arbitrary field `k`, for a given marked point.

## What made this possible, and what it does *not* discharge

The `k̄` restriction was never in Milne's argument. `Albanese/AlbaneseFromData.lean` proves
the factorisation in an arbitrary `CartesianMonoidalCategory`; the two geometric inputs it
consumes are Milne §I.1 Corollaries 1.4 and 1.2, and both are now available over an
arbitrary field (`Albanese/AVRigidityArbitraryField.lean`: commutativity is mathlib's
Stacks 0BFD, and pointed rigidity descends along `Over.pullback` because `IsMonHom` is a
pair of equations). So `isAlbanese_pic0Et`'s docstring pricing of the passage from `k̄` to
`k` as "the Galois-descent step of cluster `G`" overcharges for *this* step: no descent of
the universal property is needed, because the argument never needed the hypothesis.

**Consumer side only, and the distinction is load-bearing.** The field hypothesis is
removable on the two rigidity *inputs* the engine consumes. It remains load-bearing where
the descent datum is *manufactured*: the only geometric supply route,
`exists_unique_descent_of_section` / `_of_birational` (`AlbaneseFromData.lean:266`, `:312`),
sits under `[IsAlgClosed kbar]`, as does its engine `extend_to_av` through
`DenseOpenDescent.lean`. These files do not touch that route. So the honest form is "the
field is removable on the inputs, not yet on the supply", and a reader must not read the
paragraph above as "the field is no longer a reason this leaf is open".

**This is not a discharge of `isAlbanese_pic0Et`, and the antecedents below are not
witnessed for any curve.** What is still owed, at any base field:

1. `SymPowData C g` — the symmetric power `Sym^g C` with its symmetrisation projection,
   equivalently `HasColimit (permDiagram C g)`. This is the object the whole leg is
   blocked on (`AJC.albanese.symmetric`); the geometry is the cocycle agreement of the
   chart quotients plus `OrbitsInAffineOpen` for the curve;
2. `hdesc` — the descent datum, **for every target abelian variety `A`**. Over `k̄` this
   is supplied geometrically from a section of `f^{(g)}` over a dense open (Milne
   III.5.1(a) birationality, `exists_unique_descent_of_section`); that supply route is
   itself stated over `k̄` and is *not* transported here;
3. `aj`, `f`, `hf`, `haj0` — the Abel–Jacobi map and its symmetrisation. For the étale
   tower these must additionally be carried from `Pic0Scheme` to `Pic0SchemeEt`.

Genus `0` is **not** reached by these theorems, and an earlier version of this header
claimed it was "covered by taking `g = 0`". That is false: both statements take
`i₀ : Fin g`, and `Fin 0` is empty, so at `g = 0` they are *unapplicable* rather than
trivially true. The genus-`0` case of the headline leaf is Mumford §4 rigidity and is not
addressed here.

## Main results

* `albanese_up_of_symPowData_arbitraryField` — the unique-factorisation statement over an
  arbitrary field, matching `albanese_universal_property_of_symPowData_generic` with the
  `[IsAlgClosed]` binder deleted.
* `isAlbanese_of_symPowData_arbitraryField` — the same content packaged as `IsAlbanese`,
  i.e. in the shape `isAlbanese_pic0Et` and `JacobianWitness.isAlbaneseFor` consume. Note
  `IsAlbanese` quantifies over the target `A`, so the descent datum is required uniformly
  in `A`; that is visible in the hypothesis and is the honest form of the obligation.

## References

Milne, *Abelian Varieties*, §III.6 Proposition 6.1; §I.1 Corollaries 1.2 and 1.4.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- **Milne III.6.1 over an arbitrary base field.**

Same statement as `albanese_universal_property_of_symPowData_generic`
(`Albanese/AlbaneseJacobian.lean`) with the `[IsAlgClosed kbar]` binder deleted: for any
object `C`, any `g`, any symmetric-power datum, and any two abelian varieties `J`, `A` over
`k`, a pointed `φ : C ⟶ A` factors uniquely through a pointed `aj : C ⟶ J` whose
symmetrisation is `f`, given the descent datum.

The proof is the same call to `exists_unique_albanese_factorisation`; only the two rigidity
inputs change, to the arbitrary-field forms. -/
theorem albanese_up_of_symPowData_arbitraryField
    (C : Over (Spec (.of k))) (g : ℕ)
    (D : SymPowData C g)
    (hproj : ∀ σ : Equiv.Perm (Fin g), permAut C σ ≫ D.proj = D.proj)
    (P0 : 𝟙_ (Over (Spec (.of k))) ⟶ C) (i₀ : Fin g)
    {J A : Over (Spec (.of k))}
    [GrpObj J] [IsProper J.hom] [Smooth J.hom] [GeometricallyIrreducible J.hom]
    [GrpObj A] [IsProper A.hom] [Smooth A.hom] [GeometricallyIrreducible A.hom]
    (φ : C ⟶ A) (hφ : P0 ≫ φ = η[A])
    (aj : C ⟶ J) (f : D.carrier ⟶ J)
    (hf : letI : IsCommMonObj J := isCommMonObj_of_package_arbitraryField J
      D.proj ≫ f = powSum g aj)
    (haj0 : P0 ≫ aj = η[J])
    (hdesc : letI : IsCommMonObj A := isCommMonObj_of_package_arbitraryField A
      ∃! ψ : J ⟶ A, D.symAVMap φ = f ≫ ψ) :
    ∃! ψ : J ⟶ A, φ = aj ≫ ψ := by
  letI : IsCommMonObj J := isCommMonObj_of_package_arbitraryField J
  letI : IsCommMonObj A := isCommMonObj_of_package_arbitraryField A
  exact exists_unique_albanese_factorisation D f P0 i₀ hproj aj hf haj0 φ hφ
    (fun ψ hψ => isMonHom_of_pointed_arbitraryField ψ hψ) hdesc

/-- **`IsAlbanese` over an arbitrary base field, from the symmetric power and the descent
datum.**

This is the shape of the headline's fifth obligation `isAlbanese_pic0Et`: `J` *is* the
Albanese of the pointed curve `(C, P)`, over an arbitrary `k`, with no hypothesis on
`C(k)`.

The universal morphism is the given `aj`. Because `IsAlbanese` quantifies over the target
`A`, the descent datum is needed **uniformly in `A`** — that is the `hdesc` binder, and it
is stated that way deliberately rather than for one `A`: a version taking the datum for a
single target would not produce `IsAlbanese`.

What this reduces the obligation to is items 1–3 of the module header, none of which is
witnessed here **for a curve**. It is a reduction of the leaf's *field* hypothesis, not of
its content.

**The non-vacuity statement is per-`C`, not per-`g`.** An earlier version of this docstring
said "no `SymPowData C g` exists in this development for `g ≥ 2`". That is false, and
`SymPowColimit.lean:344–352` exists precisely to correct the unqualified form of it: at a
*terminal* `C` the permutation automorphism is the identity
(`permAut_eq_id_of_isTerminal`), so `symPowDataTrivial` (`SymPowInterface.lean:332`)
together with `hproj` inhabits the pair at **every** `g`, over an arbitrary field. So this
theorem does have inhabitants — they are just not curves.

What is open is the *curve* case, and there the obstruction is exactly
`HasColimit (permDiagram C g)` (`AJC.albanese.symmetric`): a curve has enough points to
separate the projections (`permAut_swap_ne_id_of_points`), which is what makes `hproj`
demand something at `g ≥ 2`. Read the reduction as: the field is gone, the symmetric power
of the curve is not.

`C` carries **no** curve hypotheses here, deliberately. A first version bound
`[SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]`;
all three were unused — the same one-line proof elaborates without them — so they were
decorative and made the statement look curve-specific when Milne's argument, once the
symmetric power is given, never uses that `C` is a curve. -/
theorem isAlbanese_of_symPowData_arbitraryField
    (C : Over (Spec (.of k)))
    (g : ℕ) (D : SymPowData C g)
    (hproj : ∀ σ : Equiv.Perm (Fin g), permAut C σ ≫ D.proj = D.proj)
    (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) (i₀ : Fin g)
    (J : Over (Spec (.of k)))
    [GrpObj J] [IsProper J.hom] [Smooth J.hom] [GeometricallyIrreducible J.hom]
    (aj : C ⟶ J) (f : D.carrier ⟶ J)
    (hf : letI : IsCommMonObj J := isCommMonObj_of_package_arbitraryField J
      D.proj ≫ f = powSum g aj)
    (haj0 : P ≫ aj = η[J])
    (hdesc : ∀ (A : Over (Spec (.of k))) [GrpObj A] [IsProper A.hom] [Smooth A.hom]
      [GeometricallyIrreducible A.hom] (φ : C ⟶ A),
      letI : IsCommMonObj A := isCommMonObj_of_package_arbitraryField A
      ∃! ψ : J ⟶ A, D.symAVMap φ = f ≫ ψ) :
    IsAlbanese C P J := by
  refine ⟨aj, haj0, ?_⟩
  intro A _ _ _ _ φ hφ
  letI : IsCommMonObj J := isCommMonObj_of_package_arbitraryField J
  letI : IsCommMonObj A := isCommMonObj_of_package_arbitraryField A
  exact exists_unique_albanese_factorisation D f P i₀ hproj aj hf haj0 φ hφ
    (fun ψ hψ => isMonHom_of_pointed_arbitraryField ψ hψ) (hdesc A φ)

/-! ## The non-vacuity probe, compiler-checked

The theorems above quantify over `(D, hproj)`, and a docstring claim about which `(D, hproj)`
exist is exactly the kind of claim this project has got wrong before — `SymPowInterface.lean`
made the unqualified version and `SymPowColimit.lean:344–352` is the correction. So the
statement is made here as a *theorem* rather than left as prose. -/

/-- **The `(D, hproj)` pair is inhabited at every `g`, over an arbitrary field** — so the
theorems above are not vacuous, and the honest reading of what is open is per-`C`.

The witness is `symPowDataTrivial` at a *terminal* `C`, where `permAut C σ = 𝟙`
(`permAut_eq_id_of_isTerminal`) because any two morphisms into a terminal object agree.

This is emphatically **not** progress on the curve case: at an object with enough points to
separate the projections (`permAut_swap_ne_id_of_points`) the trivial datum fails `hproj`,
and for a curve the pair is exactly what `HasColimit (permDiagram C g)` supplies and nobody
has built. The lemma exists so that "no inhabitant" is never again asserted unqualified. -/
theorem exists_symPowData_hproj_tensorUnit (g : ℕ) :
    ∃ D : SymPowData (𝟙_ (Over (Spec (.of k)))) g,
      ∀ σ : Equiv.Perm (Fin g),
        permAut (𝟙_ (Over (Spec (.of k)))) σ ≫ D.proj = D.proj := by
  refine ⟨symPowDataTrivial _ g, fun σ => ?_⟩
  rw [CategoryTheory.permAut_eq_id_of_isTerminal
    (CartesianMonoidalCategory.isTerminalTensorUnit) σ, Category.id_comp]

end AlgebraicGeometry
