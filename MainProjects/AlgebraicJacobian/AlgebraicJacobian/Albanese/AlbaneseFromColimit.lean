/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Albanese.SymPowColimit
import AlgebraicJacobian.Albanese.AlbaneseFromData

/-!
# Milne III.6.1 with the symmetric power *constructed*, not assumed

`Albanese/AlbaneseFromData.lean` proves the Albanese universal property over the interface
`SymPowData` — but takes the interface **as a hypothesis**, together with its symmetry
`hproj`. `Albanese/SymPowColimit.lean` then identifies that pair with a colimit of the
permutation action. This file composes the two, so the capstone no longer takes a
symmetric-power argument at all.

## What changes

`exists_unique_albanese_of_scheme_colimits` states Milne III.6.1 with

* **no `SymPowData` argument** — the symmetric power is `symPowOfColimit C g`;
* **no `hproj` argument** — the symmetry is discharged internally by
  `symPowOfColimit_proj_perm`, i.e. by `colimit.w`;
* one typeclass hypothesis in their place: `HasColimit (permDiagram C g)`.

That hypothesis is the honest residue of the whole leg, and by
`hasColimit_permDiagram_iff` it is *equivalent* to what the previous statement assumed —
so nothing was strengthened in the trade.

**Read the binder precisely, because an earlier draft of this file got it wrong.** It is
`HasColimit (permDiagram C g)`: **one** diagram, for **this** curve and **this** `g`, in
`Over (Spec k̄)`. It is *not*
`HasColimitsOfShape (SingleObj (Equiv.Perm (Fin g))) Scheme` — that says every such diagram
over every scheme has a colimit, which is strictly stronger, is *not* what
`hasColimit_permDiagram_iff` covers, and is in fact believed **false** at this pin
(`Albanese/SymPowColimit.lean` §6: schemes have no coequalizers in general, and a quotient
by an equivalence relation need be only an algebraic space). A hypothesis nobody can satisfy
would make this theorem vacuously true at every call site and its "single open obligation"
undischargeable in principle. The per-diagram binder is satisfiable — one curve, one `g` —
and is exactly the one the equivalence theorem names.

## What is still assumed, and why it is not this leg's debt

Milne III.5.1(a) birationality of `f^{(g)}`, in the same explicit form
`AlbaneseFromData.lean` already used: a section over a dense open, a retraction, dominance,
two density facts, and the structure-map compatibility `hover`. Those are hypotheses here
too. They are geometry about the *Jacobian*, downstream of the Picard seam, and the
`ajc-pic0av` lane owns their inputs.

## References

Milne, *Abelian Varieties*, §III.6 Proposition 6.1, p. 104; §III.5 Theorem 5.1(a), p. 101.
Blueprint `thm:albanese_universal_property`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

variable {kbar : Type u} [Field kbar] [IsAlgClosed kbar]

/-- **Milne Proposition III.6.1, with the symmetric power constructed.**

Identical to `exists_unique_albanese_factorisation_of_birational` except that the
symmetric-power interface and its symmetry hypothesis are gone: the symmetric power is
`symPowOfColimit C g`, a colimit of the `S_g`-action on `C^g`, and its projection's
symmetry is `colimit.w`.

The remaining hypotheses are exactly Milne III.5.1(a)'s birationality data, unchanged from
the sibling statement. The one typeclass hypothesis `HasColimit (permDiagram C g)` — the
colimit of the `S_g`-action on `C^g`, for this curve and this `g` — is this leg's single
open obligation, and it is equivalent, not merely sufficient, to the datum previously
assumed (`hasColimit_permDiagram_iff`). See the module header for why the *shape-quantified*
form would have been the wrong binder.

Axiom-clean. -/
theorem exists_unique_albanese_of_scheme_colimits
    {C : Over (Spec (.of kbar))} {g : ℕ}
    [HasColimit (permDiagram C g)]
    (P0 : 𝟙_ (Over (Spec (.of kbar))) ⟶ C) (i₀ : Fin g)
    {J A : Over (Spec (.of kbar))}
    [GrpObj J] [IsProper J.hom] [Smooth J.hom] [GeometricallyIrreducible J.hom]
    [IsIntegral J.left] [IsReduced J.left]
    [GrpObj A] [IsProper A.hom] [Smooth A.hom] [GeometricallyIrreducible A.hom]
    [IsReduced ((symPowOfColimit C g).carrier).left]
    (φ : C ⟶ A) (hφ : P0 ≫ φ = η[A])
    (aj : C ⟶ J) (f : (symPowOfColimit C g).carrier ⟶ J)
    (hf : letI : IsCommMonObj J := isCommMonObj_of_isProper_smooth_of_package J
      (symPowOfColimit C g).proj ≫ f = powSum g aj)
    (haj0 : P0 ≫ aj = η[J])
    (hfd : IsDominant f.left)
    (V : J.left.Opens) (hV : Dense (V : Set J.left))
    (hVpre : Dense ((f.left ⁻¹ᵁ V : ((symPowOfColimit C g).carrier).left.Opens) :
      Set ((symPowOfColimit C g).carrier).left))
    (s : (V : Scheme) ⟶ ((symPowOfColimit C g).carrier).left) (hs : s ≫ f.left = V.ι)
    (hsr : f.left.resLE V (f.left ⁻¹ᵁ V) le_rfl ≫ s = (f.left ⁻¹ᵁ V).ι)
    (hover : letI : IsCommMonObj A := isCommMonObj_of_isProper_smooth_of_package A
      (Scheme.PartialMap.mk V hV
          (s ≫ ((symPowOfColimit C g).symAVMap φ).left)).toRationalMap.compHom A.hom
        = J.hom.toRationalMap) :
    ∃! ψ : J ⟶ A, φ = aj ≫ ψ :=
  exists_unique_albanese_factorisation_of_birational (symPowOfColimit C g)
    (symPowOfColimit_proj_perm C g) P0 i₀ φ hφ aj f hf haj0 hfd V hV hVpre s hs hsr hover

end AlgebraicGeometry
