/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartCoverageIndexSlack
import AlgebraicJacobian.RiemannRoch.EffectiveUniqueness

/-!
# The chart locus SUPPLIES GAP-2's binders rather than needing them

Seven files cite the keystone by name (measured, case-insensitively, at HEAD: `Pic0ChartLocus`,
`Pic0ChartUnivReduce`, `Pic0ChartPair`, `Pic0ChartAbelNonInjective`, `Pic0ChartAbelForkReduce`,
`JacobianDataAbelDegreeWindow`, and `RiemannRoch/EffectiveUniqueness` itself); the chart-layer
ones name the *relative form of DAT-C GAP-2* as the residue of
`ChartFibrePresented.exists_factor` (`Pic0ChartOpenImmersionCriterion.lean:140`; that file is
**outside this one's import closure**, so the name is unresolvable here and is cited by
location rather than bare — `I-1173`), and price its field-level keystone
`Scheme.CurveDivisor.eq_of_picClass_eq_of_h0_one` (`RiemannRoch/EffectiveUniqueness.lean:144`)
as landed-but-unfed: what a lane still owes, they say, are that keystone's three binders
`hD`, `hD'` (effectivity) and `hone` (`h⁰ = 1`).

**On the chart locus all three are consequences.**  The reason is visible in the definition
and was apparently never read off it: `chartLocus` is *defined* by the very vanishing the rank
anchor consumes.  `IsSplitWitness` (`Pic0ChartLocus.lean:151`) asserts, at a point, the
existence of a finite separable `L/κ(t)`, a presenting Čech class `M`, and a `CurveDivisor W`
in that class with `Subsingleton H¹(𝒪(W))`.  So membership already carries a divisor with
`h¹ = 0`; what it does not carry is that divisor's *degree*, and the degree comes from
outside, from the chart-index constraint.

## The chain, every link landed before this file

1. `classDeg_presenting_eq_degAff` (`Pic0ChartCoverageDegreeStep2.lean:85`) reads the
   `L`-degree of the presenting class as the plus-degree of the class it presents;
2. the twist ledger (`chartTwist` unfolded through `degAt_mul`/`degAt_inv`/
   `degAt_thetaFamily_pow`/`degAt_sigmaFamily`) turns that into `m·d₁ − deg_k Z`, which the
   chart-index constraint `hdeg` makes exactly `n`;
3. `chi_relCurve_baseField` transports `χ(𝒪) = 1 − n` to the base-changed curve;
4. the rank anchor `h0_eq_deg_add_chi_of_subsingleton_hModule_one`
   (`RiemannRoch/FLVClass.lean:412`) gives `h⁰ = deg + χ = n + (1 − n) = 1`;
5. `exists_effective_of_h0_pos` (`RiemannRoch/SectionBound.lean:175`) then produces an
   **effective** divisor of the same class, so effectivity is free too;
6. `h0_divisorSheaf_eq_of_picClass_eq` (`RiemannRoch/ClassCohomology.lean:89`) carries the
   `h⁰` value across to it.

## What this is NOT

* It is **not** `hb_forces_h0_eq_one` (`Pic0ChartCoverageIndexSlack.lean:180`).  That takes a
  *threshold* hypothesis — every divisor of degree `≥ n` has `H¹ = 0` — which its own file
  proves **false** at `n = g` (a moving degree-`g` family has `h⁰ ≥ 2`).  Nothing here assumes
  a threshold: the vanishing is supplied by the locus at **one** divisor, the one the
  membership witness names.  A statement about one divisor of degree `n` is not a statement
  about all of them, and only the former is true.
* It does **not** discharge `exists_factor`, and therefore closes no antecedent of
  `pic0RepresentableByOfCharts`.  Everything here is **fibrewise**: it lives over a splitting
  field `L/κ(t)` at a single point `t`.  Per the standing caveat of
  `Pic0ChartAbelNonInjective.lean`, uniqueness of the *fibre* witness is not injectivity of
  the chart at a general test — the gap measured as `RelPicSeparatesDivFamZar`
  (`Pic0ChartAbelForkReduce.lean:237`, also outside this file's closure).  What is removed is
  one *named input* of the field-level keystone, not the relativisation.
* `n = genus C` is **not** proved here and is not assumed either: `n` is whatever the chart
  index is legal at, and `hχ : χ(𝒪_C) = 1 − n` is a hypothesis.  Per `I-1176`,
  `chi_moduleKSheaf` *converts* that pinning rather than supplying it, so the binder stays
  explicit and its supplier stays named.

## Main declarations

* `h0_eq_one_of_subsingleton_of_deg` — the rank anchor at a witness of the pinned degree.
* `exists_splitting_h0_eq_one_of_mem_chartLocus` — **the converse of
  `mem_chartLocus_of_witness_h1`**: from locus membership, a witness with `h⁰ = 1`.
* `eq_of_picClass_eq_of_deg_of_subsingleton` — the keystone with `hone` discharged.
* `exists_effective_picClass_eq_of_h0_eq_one` — effectivity is free once `h⁰ = 1`.
* `existsUnique_effective_of_mem_chartLocus` — **the payoff**: at a locus point the class has
  an effective representative that is the unique one, with all three keystone binders supplied.
-/

set_option autoImplicit false
/- Statements mix `relCurve C L` with the product spelling `(C ⊗ overSpec k L).left`. -/
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161). -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open TopologicalSpace Opposite

namespace AlgebraicGeometry

open AlgebraicJacobian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

noncomputable section

/-- **The rank anchor at a witness of the pinned degree.** -/
theorem h0_eq_one_of_subsingleton_of_deg
    {L : Type u} [Field L] [Algebra k L]
    [IsIntegral (relCurve C L)]
    [SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (CommRingCat.of L))]
    [QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L))]
    [Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 0)]
    [Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 1)]
    (n : ℕ) (hχ : Sheaf.chi (((C ⊗ overSpec k L).left).moduleKSheaf L) = 1 - (n : ℤ))
    (W : ((C ⊗ overSpec k L).left).CurveDivisor)
    (hW : Scheme.CurveDivisor.deg L W = (n : ℤ))
    (h1 : Subsingleton (Sheaf.HModule ((C ⊗ overSpec k L).left.divisorSheaf L W) 1)) :
    Sheaf.h0 ((C ⊗ overSpec k L).left.divisorSheaf L W) = 1 := by
  have hanchor := h0_eq_deg_add_chi_of_subsingleton_hModule_one (K := L) W h1
  rw [hW, hχ] at hanchor
  omega

/-- **THE CONVERSE OF `mem_chartLocus_of_witness_h1`, WITH THE `h⁰` VALUE READ OFF.** -/
theorem exists_splitting_h0_eq_one_of_mem_chartLocus
    {T : Over (Spec (.of k))} (lam : picEt C T) (t : T.left)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor) (n : ℕ)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ))
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (n : ℤ))
    (hlam : degAt lam (Over.testPoint t) = 0)
    (ht : t ∈ chartLocus C m Z lam) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (_ : Algebra (Over.testPointField t) L)
        (_ : IsScalarTower k (Over.testPointField t) L)
        (_ : Module.Finite (Over.testPointField t) L)
        (_ : Algebra.IsSeparable (Over.testPointField t) L)
        (M : (relCurve C L).CechPic)
        (W : ((C ⊗ overSpec k L).left).CurveDivisor),
      -- `M` presents the TWISTED fibre class at `t`: this is what ties the conclusion to
      -- `lam`, `m`, `Z` and `t`, and without it the statement is satisfied by `W = 0`.
      PicEtAff.map C L
          (picEtAffineEquiv C (Over.testPointField t)
            (picEtMap C (Over.testPoint t) (chartTwist C m Z T lam)))
        = PicEtAff.unit C L (relPicMk C (overSpec k L) M) ∧
      Scheme.CurveDivisor.picClass L W = M ∧
      Scheme.CurveDivisor.deg L W = (n : ℤ) ∧
      Sheaf.h0 ((C ⊗ overSpec k L).left.divisorSheaf L W) = 1 := by
  obtain ⟨L, hLf, hLa, hLKa, hLtow, hLfin, hLsep, M, hM, W, hWcl, hWh1⟩ := ht
  haveI : IsIntegral (relCurve C L) := instIsIntegralBaseChange C L
  haveI : SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (CommRingCat.of L)) :=
    instSmoothOfRelativeDimensionBaseChange C L
  haveI : QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L)) :=
    instQuasiCompactBaseChange C L
  haveI : Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 0) :=
    instModuleFiniteHModuleZeroBaseChange C L
  haveI : Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 1) :=
    instModuleFiniteHModuleOneBaseChange C L
  -- the witness has degree exactly `n`: its class is the presenting class of the twisted
  -- fibre class, whose `classDeg` the ledger computes as `m·d₁ − deg Z = n`.
  have hWdeg : Scheme.CurveDivisor.deg L W = (n : ℤ) := by
    rw [← classDeg_picClass (K := L) W, hWcl,
      classDeg_presenting_eq_degAff C L _ M hM]
    change degAt (chartTwist C m Z T lam) (Over.testPoint t) = (n : ℤ)
    rw [chartTwist, degAt_mul, degAt_inv, degAt_mul, degAt_thetaFamily_pow,
      degAt_sigmaFamily, hlam, hdeg]
    ring
  -- `χ(𝒪)` transports to the base-changed curve
  have hχL : Sheaf.chi (((C ⊗ overSpec k L).left).moduleKSheaf L) = 1 - (n : ℤ) :=
    chi_relCurve_baseField C L n hχ
  exact ⟨L, hLf, hLa, hLKa, hLtow, hLfin, hLsep, M, W, hM, hWcl, hWdeg,
    h0_eq_one_of_subsingleton_of_deg n hχL W hWdeg hWh1⟩

/-- **GAP-2 UNIQUENESS AT A WITNESS OF THE PINNED DEGREE** — the keystone with its `h⁰`
binder discharged rather than assumed. -/
theorem eq_of_picClass_eq_of_deg_of_subsingleton
    {L : Type u} [Field L] [Algebra k L]
    [IsIntegral (relCurve C L)]
    [SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (CommRingCat.of L))]
    [QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L))]
    [Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 0)]
    [Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 1)]
    (n : ℕ) (hχ : Sheaf.chi (((C ⊗ overSpec k L).left).moduleKSheaf L) = 1 - (n : ℤ))
    (W W' : ((C ⊗ overSpec k L).left).CurveDivisor)
    (hW : Scheme.CurveDivisor.deg L W = (n : ℤ))
    (h1 : Subsingleton (Sheaf.HModule ((C ⊗ overSpec k L).left.divisorSheaf L W) 1))
    (hWe : 0 ≤ W) (hW'e : 0 ≤ W')
    (hcl : Scheme.CurveDivisor.picClass L W = Scheme.CurveDivisor.picClass L W') :
    W' = W :=
  Scheme.CurveDivisor.eq_of_picClass_eq_of_h0_one (K := L) hWe hW'e hcl
    (h0_eq_one_of_subsingleton_of_deg n hχ W hW h1)

/-- **EFFECTIVITY IS FREE ONCE `h⁰ = 1`** — so the locus supplies GAP-2's `hD` too, and not
only its `hone`. -/
theorem exists_effective_picClass_eq_of_h0_eq_one
    {L : Type u} [Field L] [Algebra k L]
    [IsIntegral (relCurve C L)]
    [SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (CommRingCat.of L))]
    [QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L))]
    (W : ((C ⊗ overSpec k L).left).CurveDivisor)
    (h : Sheaf.h0 ((C ⊗ overSpec k L).left.divisorSheaf L W) = 1) :
    ∃ E : ((C ⊗ overSpec k L).left).CurveDivisor, 0 ≤ E ∧
      Scheme.CurveDivisor.picClass L E = Scheme.CurveDivisor.picClass L W :=
  exists_effective_of_h0_pos (K := L) W (by omega)

/-- **THE UNIQUE EFFECTIVE REPRESENTATIVE AT A LOCUS POINT** — the whole of GAP-2's
field-level content, with every one of the keystone's three binders supplied by the locus. -/
theorem existsUnique_effective_of_mem_chartLocus
    {T : Over (Spec (.of k))} (lam : picEt C T) (t : T.left)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor) (n : ℕ)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ))
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (n : ℤ))
    (hlam : degAt lam (Over.testPoint t) = 0)
    (ht : t ∈ chartLocus C m Z lam) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (_ : Algebra (Over.testPointField t) L)
        (_ : IsScalarTower k (Over.testPointField t) L)
        (_ : Module.Finite (Over.testPointField t) L)
        (_ : Algebra.IsSeparable (Over.testPointField t) L)
        (M : (relCurve C L).CechPic)
        (E : ((C ⊗ overSpec k L).left).CurveDivisor),
      -- `M` presents the TWISTED fibre class at `t`, and `E` represents `M` itself.  Without
      -- these two clauses the statement is satisfied by `L = κ(t)`, `E = 0` on any curve.
      PicEtAff.map C L
          (picEtAffineEquiv C (Over.testPointField t)
            (picEtMap C (Over.testPoint t) (chartTwist C m Z T lam)))
        = PicEtAff.unit C L (relPicMk C (overSpec k L) M) ∧
      Scheme.CurveDivisor.picClass L E = M ∧
      Scheme.CurveDivisor.deg L E = (n : ℤ) ∧
      0 ≤ E ∧
        ∀ E' : ((C ⊗ overSpec k L).left).CurveDivisor, 0 ≤ E' →
          Scheme.CurveDivisor.picClass L E' = M → E' = E := by
  obtain ⟨L, hLf, hLa, hLKa, hLtow, hLfin, hLsep, M, hM, W, hWcl, hWh1⟩ := ht
  haveI : IsIntegral (relCurve C L) := instIsIntegralBaseChange C L
  haveI : SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (CommRingCat.of L)) :=
    instSmoothOfRelativeDimensionBaseChange C L
  haveI : QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L)) :=
    instQuasiCompactBaseChange C L
  haveI : Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 0) :=
    instModuleFiniteHModuleZeroBaseChange C L
  haveI : Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 1) :=
    instModuleFiniteHModuleOneBaseChange C L
  have hWdeg : Scheme.CurveDivisor.deg L W = (n : ℤ) := by
    rw [← classDeg_picClass (K := L) W, hWcl,
      classDeg_presenting_eq_degAff C L _ M hM]
    change degAt (chartTwist C m Z T lam) (Over.testPoint t) = (n : ℤ)
    rw [chartTwist, degAt_mul, degAt_inv, degAt_mul, degAt_thetaFamily_pow,
      degAt_sigmaFamily, hlam, hdeg]
    ring
  have hχL : Sheaf.chi (((C ⊗ overSpec k L).left).moduleKSheaf L) = 1 - (n : ℤ) :=
    chi_relCurve_baseField C L n hχ
  have hone : Sheaf.h0 ((C ⊗ overSpec k L).left.divisorSheaf L W) = 1 :=
    h0_eq_one_of_subsingleton_of_deg n hχL W hWdeg hWh1
  -- the effective representative of the SAME class, and its own `h⁰`/vanishing data
  obtain ⟨E, hEe, hEcl⟩ := exists_effective_picClass_eq_of_h0_eq_one W hone
  -- `E` represents `M` too, has the same degree, and inherits `h⁰ = 1`
  have hEM : Scheme.CurveDivisor.picClass L E = M := hEcl.trans hWcl
  have hEone : Sheaf.h0 ((C ⊗ overSpec k L).left.divisorSheaf L E) = 1 := by
    rw [h0_divisorSheaf_eq_of_picClass_eq (K := L) hEcl]; exact hone
  have hEdeg : Scheme.CurveDivisor.deg L E = (n : ℤ) :=
    (deg_eq_deg_of_picClass_eq (K := L) hEcl).trans hWdeg
  refine ⟨L, hLf, hLa, hLKa, hLtow, hLfin, hLsep, M, E, hM, hEM, hEdeg, hEe,
    fun E' hE'e hcl => ?_⟩
  exact Scheme.CurveDivisor.eq_of_picClass_eq_of_h0_one (K := L) hEe hE'e
    (hEM.trans hcl.symm) hEone

/-! ## The non-vacuity check: the strengthened conclusion gives membership back

An earlier version of the two theorems above stated only `h⁰ = 1` (and effectivity) under an
existential over *both* the field and the divisor, mentioning neither `M` nor the twisted
class.  That was **VACUOUS** and a fresh-context audit refuted it (`I-1233`): taking
`L = κ(t)` — every instance binder is `inferInstance` — and `W = 0` gives
`h⁰(𝒪) = 1` unconditionally on any curve, so the statement held with `ht`, `hdeg`, `hχ` and
`hlam` all unused.  The repair was to move the *relations* into the conclusion, which the
proof bodies already established and then discarded.

This section is the check that the repair is sufficient rather than merely longer: the
strengthened conclusion **implies** `t ∈ chartLocus C m Z lam`, so it is equivalent to
membership and cannot be satisfied by a trivial divisor on a curve where the locus is empty. -/

/-! ### Why the repair is sufficient, and the one check I did NOT get to compile

The clauses now in the conclusion are, verbatim, the first three clauses of `IsSplitWitness`
(`Pic0ChartLocus.lean:151-161`): `hM` is its presentation equation, `picClass L W = M` its
class clause, and the vanishing its third.  So the strengthened conclusion **contains** the
membership data rather than merely being implied by it, and the `W = 0` inhabitant is excluded
— on a curve where the locus at `t` is empty, no `(M, W)` satisfying `hM` and the class clause
exists at all.

**What I could not land, stated because it is the honest form of the non-vacuity check.**  The
sharp statement is the *converse* — that `(hM, picClass L W = M, Subsingleton H¹)` implies
`t ∈ chartLocus C m Z lam` — which is `mem_chartLocus_of_isSplitWitness_fibre` applied to the
anonymous constructor of `IsSplitWitness`.  Mathematically it is the identity function on the
data.  It does **not** elaborate here: unifying seven instance binders (`Field L`,
`Algebra k L`, `Algebra κ(t) L`, the tower, finiteness, separability) against this file's
section context exceeds `isDefEq` at 1.6M heartbeats.  That is a defeq wall of the
`relCurve`-vs-product spelling, not a mathematical gap, and I am recording it rather than
raising the budget further or leaving a `sorry` in a rooted file.  A lane wanting the
biconditional should state it in `Pic0ChartLocus.lean` itself, where the instance context is
already the one `IsSplitWitness` was declared in. -/

end

end AlgebraicGeometry
