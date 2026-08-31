/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.FiberH0Comparison

/-!
# The fibre `h⁰` is the fibrewise Čech kernel — with no base-change hypothesis

**A repricing, and it corrects obligation (a) of the three recorded at
`Picard/FiberH0Comparison.lean`:79-82.**

`fiberRank_gammaTop_eq_fiberH0` (same file) proves

```
dim_κ(t) (κ(t)-fibre of Γ(p_* M, ⊤))  =  p.fiberH0 M t
```

assuming `hbc`: bijectivity of `TwoTerm.kerBaseChange` over **every** algebra.
That hypothesis was recorded as the honest half of cohomology-and-base-change,
not free, with a counterexample showing it fails without surjectivity of the
differential (`A = ℤ`, `d = ·2`, `B = ℤ/2`).  All of that is correct.

What was **not** noticed: `hbc` is consumed in exactly one place, *step 3*, whose
only job is to move from `κ(t) ⊗ ker d` to `ker (d ⊗ κ(t))` — i.e. to reach the
pushforward's *own* section module.  Steps 4, 5 and 6 alone already prove

```
dim_κ(t) ker (d ⊗ κ(t))  =  p.fiberH0 M t
```

with **no `hbc`, no `hfin`, no `hproj`, and no `h¹`-vanishing** — where `d` is
the Čech difference map `𝒰.moduleSectionDiffBase p M`.  That is the statement
below, and it is the one a semicontinuity argument wants: the *left* side is a
kernel of a base-changed map, which is what an upper-semicontinuity engine can
say something about, whereas `Γ(p_* M, ⊤)`'s fibre is not.

So the pricing was right about `hbc` and wrong about who needs it.  `hbc` is
needed to identify the fibre of the **pushforward's sections**; it is not needed
to identify the fibre `h⁰`.  A lane routing semicontinuity through the fibrewise
Čech kernel does not owe it at all.

## What this composes with, and what remains

`AlgebraicJacobian.TwoTerm.isOpen_finrank_ker_baseChange_le`
(`Picard/TwoTermKernelSemicontinuity.lean`) proves openness of
`{t | dim ker (k ⊗ κ(t)) ≤ e}` for `k : K → Aⁿ` with `K` finitely presented
projective.  This file's theorem rewrites `p.fiberH0 M t` as exactly such a
kernel dimension.  Composing them needs two things that are **still open** and
are not supplied here:

* the Čech difference map `𝒰.moduleSectionDiffBase p M` must be *replaced* by
  one of the engine's shape (`K` projective, target `Aⁿ` free).
  `exists_twoTermFiniteReplacement` (`Picard/TwoTermFiniteFree.lean`:545)
  produces that shape from noetherian + flat terms + f.g. cohomology, but its
  `h0_bijective` field compares the replacement's `H⁰` with the original's over
  every algebra, and *that* comparison — not `hbc` — is the remaining
  cohomology-and-base-change content;
* a **carrier transport**: the engine quantifies over `t : PrimeSpectrum A` for
  a bare ring `A`, this theorem over `t : PrimeSpectrum R` with coefficient ring
  `Γ(Spec R, ⊤)`.  `Scheme.ΓSpecIso R` is an isomorphism, not an equality, so
  the transport is real work of the kind steps 2 and 6 perform by hand — the
  obligation (c) already on record.

Neither is discharged below.  What is discharged is that `hbc` is not part of
either.

## The junk-value caveat, which this file DOES inherit

An earlier revision of this docstring said the theorem holds "with no hypotheses
beyond the geometric ones" and listed what it does not need, without noting the
cost.  A fresh-context review flagged the omission, and it is a real one.

`Module.finrank` returns `0` in the infinite-dimensional case.  Here the
coefficient ring is `Γ(Spec ((Spec R).residueField t), ⊤)`, which carries no
`Field` — not even `Nontrivial` — instance in scope, and neither
`FiniteDimensional` of the fibre sections nor `Module.Finite` of the Čech kernel
is synthesisable.  So when the fibre sections are infinite-dimensional, **both
sides read `0` and the identity is vacuously true**.  That is exactly the hazard
`Picard/FiberH0Comparison.lean`:40-55 records for its own theorem, and dropping
`hfin` re-opens it here for the same reason.

This is *not* the same situation as
`Picard/TwoTermKernelSemicontinuity.lean`, which legitimately closes the hazard:
there the complex's shape (`K` finite, target `Aⁿ`) makes both fibres
finite-dimensional by synthesis.  The two files were audited to different
standards, and this paragraph is the correction.

So the honest reading: the identity is **true unconditionally and informative
where the fibre `h⁰` is finite** — which is the case of interest, since a curve's
`h⁰` is finite — but the statement does not certify that finiteness itself.  A
consumer wanting a non-vacuous reading must supply it, and doing so is *not* the
same as supplying `hbc`; that remains the point of the restatement.

## References

Stacks 02KG (cohomology and base change at `i = 0`), 00NX; Mumford, *Abelian
Varieties*, II §5; Hartshorne III 12.8.
-/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Module Limits TensorProduct

namespace AlgebraicGeometry

variable {R : CommRingCat.{u}} {X : Scheme.{u}}

/-- **The fibre `h⁰` is the dimension of the base-changed Čech kernel**, with no
base-change, finiteness or projectivity hypothesis — but see the module
docstring's junk-value caveat: with `hfin` dropped, the identity is vacuously
`0 = 0` where the fibre sections are infinite-dimensional, and it does not
certify that finiteness itself.

For quasi-compact quasi-separated `p : X ⟶ Spec R`, quasi-coherent `M` with a
two-chart affine cover `𝒰`, and `t : Spec R` with affine fibre inclusion:

```
dim_κ(t) ker (𝒰.moduleSectionDiffBase p M ⊗ κ(t))  =  p.fiberH0 M t.
```

This is steps 4-6 of `rank_pushforward_eq_fiberH0` in isolation.  Compare
`fiberRank_gammaTop_eq_fiberH0`, which reaches the fibre of `Γ(p_* M, ⊤)`
instead and needs `hbc` to do so: `hbc` is consumed only in the step that
crosses from `ker (d ⊗ κ(t))` to `κ(t) ⊗ ker d`, which this statement never
performs.  See the module docstring — this corrects the pricing of obligation
(a), it does not close it. -/
theorem finrank_ker_moduleSectionDiffBase_baseChange_eq_fiberH0
    (p : X ⟶ Spec R) (𝒰 : X.AffineCoverMVSquare) (M : X.Modules)
    [M.IsQuasicoherent] [QuasiCompact p] [QuasiSeparated p]
    (t : PrimeSpectrum R) [IsAffineHom (p.fiberι t)] :
    letI : Algebra Γ(Spec R, ⊤) Γ(Spec ((Spec R).residueField t), ⊤) :=
      (((Spec R).fromSpecResidueField t).appLE ⊤ ⊤ le_top).hom.toAlgebra
    letI := p.baseSectionsModule M 𝒰.U₁
    letI := p.baseSectionsModule M 𝒰.U₂
    letI := p.baseSectionsModule M (𝒰.U₁ ⊓ 𝒰.U₂)
    Module.finrank Γ(Spec ((Spec R).residueField t), ⊤)
        (LinearMap.ker ((𝒰.moduleSectionDiffBase p M).baseChange
          Γ(Spec ((Spec R).residueField t), ⊤)))
      = p.fiberH0 M t := by
  letI aRK : Algebra Γ(Spec R, ⊤) Γ(Spec ((Spec R).residueField t), ⊤) :=
    (((Spec R).fromSpecResidueField t).appLE ⊤ ⊤ le_top).hom.toAlgebra
  letI m1 := p.baseSectionsModule M 𝒰.U₁
  letI m2 := p.baseSectionsModule M 𝒰.U₂
  letI m0 := p.baseSectionsModule M (𝒰.U₁ ⊓ 𝒰.U₂)
  letI n1 := (p.fiberToSpecResidueField t).baseSectionsModule (p.fiberModule t M)
    ((𝒰.preimage (p.fiberι t)).U₁)
  letI n2 := (p.fiberToSpecResidueField t).baseSectionsModule (p.fiberModule t M)
    ((𝒰.preimage (p.fiberι t)).U₂)
  letI n0 := (p.fiberToSpecResidueField t).baseSectionsModule (p.fiberModule t M)
    ((𝒰.preimage (p.fiberι t)).U₁ ⊓ (𝒰.preimage (p.fiberι t)).U₂)
  letI nT := (p.fiberToSpecResidueField t).baseSectionsModule (p.fiberModule t M)
    (⊤ : (p.fiber t).Opens)
  -- STEP 4: the fibrewise Čech square (Stacks 02KG at `i = 0`, chart form).
  have step4 := finrank_ker_baseChange_residueField 𝒰 p M t
  -- STEP 5: the fibre's Čech kernel is its global sections.
  have step5 : Module.finrank Γ(Spec ((Spec R).residueField t), ⊤)
        (LinearMap.ker ((𝒰.preimage (p.fiberι t)).moduleSectionDiffBase
          (p.fiberToSpecResidueField t) (p.fiberModule t M)))
      = Module.finrank Γ(Spec ((Spec R).residueField t), ⊤)
          Γ(p.fiberModule t M, (⊤ : (p.fiber t).Opens)) :=
    (LinearEquiv.finrank_eq ((𝒰.preimage (p.fiberι t)).globalSectionsEquivKerModuleSectionDiffBase
      (p.fiberToSpecResidueField t) (p.fiberModule t M))).symm
  -- STEP 6: the semilinear transport onto `fiberH0`'s own coefficient field.
  have step6 : Module.finrank Γ(Spec ((Spec R).residueField t), ⊤)
        Γ(p.fiberModule t M, (⊤ : (p.fiber t).Opens))
      = p.fiberH0 M t := by
    letI := p.fiberSectionsModule t (p.fiberModule t M)
    refine finrank_eq_of_ringEquiv_addEquiv
      (Scheme.ΓSpecIso ((Spec R).residueField t)).commRingCatIsoToRingEquiv
      (AddEquiv.refl _) ?_
    intro r m
    change r • m = _
    rw [Scheme.Hom.baseSectionsModule_smul_def]
    change _ = ((p.fiberResidueMap t).hom
      ((Scheme.ΓSpecIso ((Spec R).residueField t)).commRingCatIsoToRingEquiv r)) • m
    congr 1
    simp only [Scheme.Hom.fiberResidueMap, CommRingCat.hom_comp, RingHom.comp_apply]
    have hLE : (p.fiberToSpecResidueField t).appLE ⊤ ⊤ le_top
        = (p.fiberToSpecResidueField t).appTop := Scheme.Hom.appLE_eq_app _
    rw [hLE]
    congr 1
    have h1 := congrArg (fun φ : Γ(Spec ((Spec R).residueField t), ⊤) ⟶
        Γ(Spec ((Spec R).residueField t), ⊤) => φ.hom r)
      (Scheme.ΓSpecIso ((Spec R).residueField t)).hom_inv_id
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id,
      RingHom.id_apply] at h1
    exact h1.symm
  rw [step4, step5, step6]

end AlgebraicGeometry
