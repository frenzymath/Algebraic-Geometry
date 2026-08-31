/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Ledger.ChiLedger

/-!
# Section drop and the `H¹` peel, on the dévissage sequence

Cluster P asks for the *section-drop* results and for `H¹` vanishing.  This file supplies the
drop layer and the exact statement of the peel, both **unconditionally** on the χ-ledger's own
carrier: the only hypotheses are the five curve binders `ChiLedger.lean` already runs on
(`Field K`, `SmoothOfRelativeDimension 1`, `IsIntegral`, `QuasiCompact`, and the two
`Module.Finite` cohomology instances, which `ChiCurve`/`Finiteness` discharge at a curve).

Everything comes off the six-term slice of the dévissage sequence
`0 → 𝒪(D − x) → 𝒪(D) → sky_x J → 0` (`Ledger/ChiSlice.lean`), whose third term has
`H¹ = 0` because it is a skyscraper.  Two slots of that slice are the whole content:

* `H⁰(𝒪(D − x)) ↪ H⁰(𝒪(D))` — `injective_map_f_zero`;
* `H¹(𝒪(D − x)) ↠ H¹(𝒪(D))` — `surjective_map_f _ 1`, available because `H¹(sky) = 0`.

## What is proved

* `h0_divisorSheaf_le_of_le`, `h1_divisorSheaf_le_of_le` — monotonicity of `h⁰` and
  antitonicity of `h¹` along a *single dévissage step*.
* `h0_sub_point_le`, `h0_le_h0_sub_point_add_residueDeg` — the **two-sided section drop**
  `h⁰(𝒪(D − x)) ≤ h⁰(𝒪(D)) ≤ h⁰(𝒪(D − x)) + [κ(x) : K]`.
* `h0_sub_h0_sub_point_add_h1_sub_h1_sub_point` — the drop **identity**: the `h⁰` gain and
  the `h¹` loss add up to the residue degree exactly.
* `subsingleton_hModule_one_of_subsingleton_sub_point` (★ the peel) — `H¹` vanishing
  **propagates upward** across a dévissage step: if `H¹(𝒪(D − x)) = 0` then `H¹(𝒪(D)) = 0`.
  AJC's *adelic* lane takes this as a hypothesis on its own carrier
  (`Adelic/BoundedVanishing.lean`'s peel datum, discharged only off the overlap); on the ledger
  carrier it is a theorem of the slice.  It is **not new to the workspace**: AJCR proves the
  same chain in `RiemannRoch/FLVClass.lean` (`peel_single`, `peel_nsmul_single`,
  `peel_effective`).  See the provenance note on `subsingleton_hModule_one_add_effective`.
* `subsingleton_hModule_one_of_le` (★) — the same statement along **any** divisor increase
  `D₀ ≤ D`, by dévissage induction: `H¹` vanishing is **upward closed on the effective cone
  above `D₀`**.  Together with `chi_divisorSheaf` this turns one vanishing into the exact
  Riemann–Roch equality `h⁰(𝒪(D)) = χ(𝒪_X) + deg D` at every `D ≥ D₀`
  (`h0_divisorSheaf_of_subsingleton_of_le`), and makes the section drop *exact*
  (`h0_eq_h0_sub_point_add_residueDeg_of_subsingleton`).

**The peel chain uses no finiteness at all.**  Eleven of the nineteen declarations below `omit` both
`Module.Finite` cohomology instances: surjectivity of a map is not a dimension count.  That
is also why the peel is stated on `Subsingleton (H¹ …)` rather than on `h¹ … = 0` — the
latter is vacuously true for an infinite-dimensional `H¹`, since `Module.finrank` reads `0`
there, so the `Subsingleton` form is both the stronger statement and the honest one.  The
`h¹`-spellings (`h1_le_h1_sub_point`, `h1_eq_zero_of_h1_sub_point_eq_zero`) do need the
finiteness, and they carry it.

## What this does NOT supply — the three cluster-P items, kept apart

Read this before quoting anything above as "uniform vanishing":

1. **Single-field bounded vanishing** — "there is `N` such that `deg D ≥ N` implies
   `h¹(𝒪(D)) = 0`".  NOT proved *in this file* and not implied by anything in it: the peel
   moves vanishing *up the divisor order* `D₀ ≤ D`, and a divisor of large *degree* need not
   dominate `D₀`.  A base vanishing `H¹(𝒪(D₀)) = 0` at even one `D₀` is an input nothing here
   produces.

   **BUT THE GAP FROM THE ORDER-CONE TO THE DEGREE HALF-SPACE IS NOW CLOSED, one import
   above.**  `Ledger/DegreeVanishing.lean` proves
   `subsingleton_hModule_one_of_deg_ge`: from **one** base vanishing at `D₀`, `H¹(𝒪(D))`
   vanishes for every `D` with `deg D ≥ deg D₀ + 1 − χ(𝒪_X)`.  An earlier version of this
   docstring called the bridging cofinality statement open and said "nothing in AJC or AJCR
   currently produces it".  That was **wrong**: the missing move was not a new input but the
   observation that the peel may be applied to a *linearly equivalent translate* of `D₀` —
   `mulEquivDivisorSheaf` (already in `Ledger/MulEquiv.lean`) makes `H¹` vanishing a class
   invariant, and `riemann_inequality` (already in `Ledger/ChiLedger.lean`) manufactures the
   translating function from `deg (D − D₀) + χ ≥ 1`.  Both were in the tree; nobody had put
   them together.  So `exists_bound_of_cofinal_vanishing` below is now a *corollary* of a
   theorem rather than a reduction to an open hypothesis — see
   `DegreeVanishing.exists_le_subsingleton_of_deg_ge`, which is exactly its `hcof`.

   **Where the base actually stands, and a correction.**  Inside *this project's* Ledger tree
   the base is unavailable: `H¹(𝒪) = 0` at `ℙ¹` would need `ledgerGenus (Adelic.p1Over k) = 0`,
   which `Ledger/NonVacuity.lean` explicitly does *not* prove (it proves the hypothesis bundle
   is inhabited — a different claim), and the tree's only `H¹`-vanishing producer,
   `AffineVanishing.Scheme.subsingleton_moduleKSheaf_hModule_one`, requires `[IsAffine X]` and
   so cannot reach a proper curve at all.

   **But the base is NOT open in the workspace.**  The sibling project
   `Algebraic-Jacobian-Challenge-Rebuild` proves a base vanishing on this very carrier:
   `RiemannRoch/FLVVanishing.subsingleton_hModule_divisorSheaf_one_of_isFinite_toP1` (:302)
   gives, for a finite dominant `π : Y ⟶ ℙ¹` compatible with the structure maps and any `D`,
   an `n₀` with `H¹(𝒪(D + n·F)) = 0` for all `n ≥ n₀`, where `F` is the fibre divisor.  An
   earlier version of this docstring said the base was open "at every curve"; that was measured
   only in AJC's own tree and is **false as a statement about the workspace** — the same
   cone-scoping error this lane has now made repeatedly.  What AJC lacks is the *import*: AJCR's
   fibre-divisor and finite-map-to-`ℙ¹` layer is not present here.  So the honest gap is a
   **port**, not an open problem, and `exists_bound_of_cofinal_vanishing` is the right shape to
   receive it — AJCR's conclusion is a tower `D + n·F`, which is exactly a cofinal family.
2. **Extension-uniformity** — a bound uniform over finite extensions `K'/K`.  Untouched:
   no statement here quantifies over a second field, and `CurveDivisor`/`residueDeg` are
   pinned to the single base field `K`.
3. **Global generation** — that `𝒪(D)` is generated by its global sections.  Untouched on
   *this* carrier: no evaluation map appears in this file.  Note that
   `h0_eq_h0_sub_point_add_residueDeg_of_subsingleton` below is a statement about
   **dimensions**, not about surjectivity of evaluation: it says the drop equals the residue
   degree, which is the numerical *shadow* of generation at `x`, not generation itself.  The
   adelic lane does prove the bridge between them (`Adelic/GlobalGeneration.lean`:
   `generatedAt_of_evalMap_surjective` and `evalMap_surjective`), but on its own `degK`
   carrier and gated on `hledger` plus two vanishings; nothing here transports it, because
   this file has no evaluation map to feed it.

So the honest summary **for this file**: the **peel** is unconditional at every closed point,
the **base** is not supplied, and the **degree threshold** is isolated as
`exists_bound_of_cofinal_vanishing`.  That last hypothesis is no longer open — it is proved in
`Ledger/DegreeVanishing.lean` from `MulEquiv` plus `riemann_inequality` — so the residual input
for the whole layer is now exactly **one** base vanishing at **one** divisor.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

open Scheme

section Drop

variable (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 1)]

/-! ## The slice of the dévissage sequence, with its skyscraper data installed

Every statement below runs the same four `haveI`s: the finiteness of the two outer terms in
each degree and the vanishing of `H¹(sky)`.  They are collected here once, in the
`devissageSES` spelling (the identifications with the divisor-sheaf spellings are
definitional, exactly as in `ChiLedger.chi_step`). -/

section Slice

variable {x : X} (hx : x ≠ genericPoint X) (D : X.CurveDivisor)

omit [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 1)] in
/-- `H⁰` of the skyscraper term of the dévissage sequence is finite. -/
private theorem moduleFinite_devissage_X₃_zero
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] :
    Module.Finite K (Sheaf.HModule (devissageSES K hx D).X₃ 0) :=
  haveI := moduleFinite_jumpModule K hx D
  moduleFinite_hModule_skyModule_zero x (jumpModule K hx D)

omit [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 1)] in
/-- `H¹` of the skyscraper term of the dévissage sequence vanishes. -/
private theorem subsingleton_devissage_X₃_one :
    Subsingleton (Sheaf.HModule (devissageSES K hx D).X₃ 1) :=
  skyModule_subsingleton_hModule_one x (jumpModule K hx D)

omit [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 1)] in
/-- **`H⁰(𝒪(D − x)) ↪ H⁰(𝒪(D))`**: a section with a smaller pole bound at `x` is a section.
The left end of the dévissage slice. -/
theorem injective_hModule_zero_divisorSheafLE :
    Function.Injective
      (Sheaf.HModule.map (devissageSES K hx D).f 0) :=
  Sheaf.HModule.injective_map_f_zero (devissageSES_shortExact K hx D)

omit [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 1)] in
/-- **`H¹(𝒪(D − x)) ↠ H¹(𝒪(D))`** (★ the peel, as a map): the dévissage map is surjective on
`H¹` because the skyscraper quotient has no `H¹`.  This is the datum that the adelic lane
takes as a hypothesis (`Adelic/BoundedVanishing.lean`); on this carrier it is a theorem. -/
theorem surjective_hModule_one_divisorSheafLE :
    Function.Surjective
      (Sheaf.HModule.map (devissageSES K hx D).f 1) :=
  haveI := subsingleton_devissage_X₃_one K hx D
  Sheaf.HModule.surjective_map_f (devissageSES_shortExact K hx D) 1

end Slice

/-! ## Monotonicity of `h⁰` and antitonicity of `h¹` across one step -/

section Step

variable {x : X} (hx : x ≠ genericPoint X) (D : X.CurveDivisor)

/-- **`h⁰` grows along a dévissage step**: `h⁰(𝒪(D − x)) ≤ h⁰(𝒪(D))`, from injectivity at
the left end of the slice. -/
theorem h0_sub_point_le :
    Sheaf.h0 (X.divisorSheaf K (D - CurveDivisor.single hx 1)) ≤
      Sheaf.h0 (X.divisorSheaf K D) := by
  have hinj := injective_hModule_zero_divisorSheafLE K hx D
  haveI : Module.Finite K (Sheaf.HModule (devissageSES K hx D).X₂ 0) :=
    inferInstanceAs (Module.Finite K (Sheaf.HModule (X.divisorSheaf K D) 0))
  exact LinearMap.finrank_le_finrank_of_injective (f := Sheaf.HModule.map
    (devissageSES K hx D).f 0) hinj

/-- **`h¹` drops along a dévissage step**: `h¹(𝒪(D)) ≤ h¹(𝒪(D − x))`, from surjectivity of
the peel map. -/
theorem h1_le_h1_sub_point :
    Sheaf.h1 (X.divisorSheaf K D) ≤
      Sheaf.h1 (X.divisorSheaf K (D - CurveDivisor.single hx 1)) := by
  have hsurj := surjective_hModule_one_divisorSheafLE K hx D
  haveI : Module.Finite K (Sheaf.HModule (devissageSES K hx D).X₁ 1) :=
    inferInstanceAs (Module.Finite K
      (Sheaf.HModule (X.divisorSheaf K (D - CurveDivisor.single hx 1)) 1))
  exact LinearMap.finrank_le_finrank_of_surjective (f := Sheaf.HModule.map
    (devissageSES K hx D).f 1) hsurj

/-- **The section drop is at most the residue degree**:
`h⁰(𝒪(D)) ≤ h⁰(𝒪(D − x)) + [κ(x) : K]`.  Read off the χ-ledger step together with
`h¹(𝒪(D)) ≤ h¹(𝒪(D − x))`: the Euler characteristic gains exactly `[κ(x) : K]`, and the
`h¹` term can only help. -/
theorem h0_le_h0_sub_point_add_residueDeg :
    Sheaf.h0 (X.divisorSheaf K D) ≤
      Sheaf.h0 (X.divisorSheaf K (D - CurveDivisor.single hx 1)) + X.residueDeg K x := by
  have hstep := chi_step K hx D
  have hmono := h1_le_h1_sub_point K hx D
  rw [Sheaf.chi, Sheaf.chi] at hstep
  omega

/-- **The drop identity**: the `h⁰` gain plus the `h¹` loss is exactly the residue degree,
`(h⁰(𝒪(D)) − h⁰(𝒪(D − x))) + (h¹(𝒪(D − x)) − h¹(𝒪(D))) = [κ(x) : K]`.  This is `chi_step`
rearranged, stated in ℤ so that both differences are honest. -/
theorem h0_sub_h0_sub_point_add_h1_sub_h1_sub_point :
    ((Sheaf.h0 (X.divisorSheaf K D) : ℤ) -
        Sheaf.h0 (X.divisorSheaf K (D - CurveDivisor.single hx 1))) +
      ((Sheaf.h1 (X.divisorSheaf K (D - CurveDivisor.single hx 1)) : ℤ) -
        Sheaf.h1 (X.divisorSheaf K D)) = X.residueDeg K x := by
  have hstep := chi_step K hx D
  rw [Sheaf.chi, Sheaf.chi] at hstep
  omega

end Step

/-! ## The peel: `H¹` vanishing propagates upward -/

section Peel

omit [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 1)] in
/-- **The peel** (★): `H¹` vanishing propagates *up* one dévissage step.  If
`H¹(𝒪(D − x)) = 0` then `H¹(𝒪(D)) = 0`, because `H¹(𝒪(D − x)) ↠ H¹(𝒪(D))`.

This is the exact statement the adelic lane carries as an unproved peel-surjectivity datum.
It is **not** single-field bounded vanishing: it moves a vanishing along the divisor order,
and produces no vanishing of its own. -/
theorem subsingleton_hModule_one_of_subsingleton_sub_point {x : X}
    (hx : x ≠ genericPoint X) (D : X.CurveDivisor)
    (h : Subsingleton (Sheaf.HModule (X.divisorSheaf K (D - CurveDivisor.single hx 1)) 1)) :
    Subsingleton (Sheaf.HModule (X.divisorSheaf K D) 1) := by
  have hsurj := surjective_hModule_one_divisorSheafLE K hx D
  haveI hsub : Subsingleton (Sheaf.HModule (devissageSES K hx D).X₁ 1) := h
  exact ⟨fun a b => by
    obtain ⟨a', rfl⟩ := hsurj a
    obtain ⟨b', rfl⟩ := hsurj b
    rw [Subsingleton.elim a' b']⟩

/-- **`h¹` version of the peel**: `h¹(𝒪(D − x)) = 0` forces `h¹(𝒪(D)) = 0`. -/
theorem h1_eq_zero_of_h1_sub_point_eq_zero {x : X} (hx : x ≠ genericPoint X)
    (D : X.CurveDivisor)
    (h : Sheaf.h1 (X.divisorSheaf K (D - CurveDivisor.single hx 1)) = 0) :
    Sheaf.h1 (X.divisorSheaf K D) = 0 := by
  have hmono := h1_le_h1_sub_point K hx D
  omega

end Peel

/-! ## Upward closure of `H¹` vanishing on the cone above a divisor

The single-step peel iterates.  The induction is `CurveDivisor.induction_devissage` applied
to the *difference* `D - D₀`, whose effectivity is what "above `D₀`" means; the predicate is
"vanishing at `D₀ + E` for the effective part of `E`". -/

section Cone

omit [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 1)] in
/-- **Additive form of the peel**: `H¹(𝒪(B)) = 0` forces `H¹(𝒪(B + x)) = 0`. -/
theorem subsingleton_hModule_one_add_single {x : X} (hx : x ≠ genericPoint X)
    (B : X.CurveDivisor)
    (h : Subsingleton (Sheaf.HModule (X.divisorSheaf K B) 1)) :
    Subsingleton (Sheaf.HModule (X.divisorSheaf K (B + CurveDivisor.single hx 1)) 1) := by
  refine subsingleton_hModule_one_of_subsingleton_sub_point K hx
    (B + CurveDivisor.single hx 1) ?_
  have heq : B + CurveDivisor.single hx 1 - CurveDivisor.single hx 1 = B := by abel
  rwa [heq]

omit [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 1)] in
/-- **Peeling a multiple of a point**: `H¹(𝒪(A)) = 0` forces `H¹(𝒪(A + n·x)) = 0`. -/
theorem subsingleton_hModule_one_add_nsmul_single {x : X} (hx : x ≠ genericPoint X)
    (A : X.CurveDivisor) (n : ℕ)
    (h : Subsingleton (Sheaf.HModule (X.divisorSheaf K A) 1)) :
    Subsingleton (Sheaf.HModule (X.divisorSheaf K (A + n • CurveDivisor.single hx 1)) 1) := by
  induction n with
  | zero => rwa [zero_nsmul, add_zero]
  | succ n ih =>
    have hstep := subsingleton_hModule_one_add_single K hx
      (A + n • CurveDivisor.single hx 1) ih
    have heq : A + n • CurveDivisor.single hx 1 + CurveDivisor.single hx 1
        = A + (n + 1) • CurveDivisor.single hx 1 := by
      rw [succ_nsmul]; abel
    rwa [heq] at hstep

omit [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 1)] in
/-- **Effective peeling**: `H¹(𝒪(A)) = 0` forces `H¹(𝒪(A + E)) = 0` for every effective `E`.
Induction on the size of the support of `E`, one multiplicity block at a time.

**PROVENANCE, CORRECTED.**  This is a **re-derivation of existing sibling-project work**, not a
new result.  `Algebraic-Jacobian-Challenge-Rebuild`'s `RiemannRoch/FLVClass.lean` already has
this exact three-step chain in the exact `Subsingleton` spelling — `peel_single`,
`peel_nsmul_single`, `peel_effective` (:260, :277, :292) — on the same variable block, from the
same `Sheaf.HModule.surjective_map_f` on `devissageSES`.  An earlier version of this docstring
said the adaptation was of `SectionBound.h1_add_effective_le` (the `finrank` *inequality*) and
that AJCR "does not have the vanishing propagation".  That was **false**, and it was found by a
fresh-context review, not by me: I checked `SectionBound.lean`, which is where the *inequality*
lives, and never opened `FLVClass.lean`, where the *propagation* lives.  See `I-0623`.

What this file does add over `FLVClass`: the `D₀ ≤ D` order form
(`subsingleton_hModule_one_of_le`), the two-sided section drop, the drop identity, exact
Riemann–Roch on the order-cone, and the cofinality reduction.  The peel chain itself is
duplicated mathematics, kept here only because AJC cannot import AJCR. -/
theorem subsingleton_hModule_one_add_effective (A E : X.CurveDivisor) (hE : 0 ≤ E)
    (h : Subsingleton (Sheaf.HModule (X.divisorSheaf K A) 1)) :
    Subsingleton (Sheaf.HModule (X.divisorSheaf K (A + E)) 1) := by
  suffices H : ∀ (n : ℕ) (E : X.CurveDivisor), 0 ≤ E → (toFinsupp E).support.card = n →
      Subsingleton (Sheaf.HModule (X.divisorSheaf K (A + E)) 1) from H _ E hE rfl
  intro n
  induction n with
  | zero =>
    intro E hE hc
    have hE0 : E = 0 := Finsupp.support_eq_empty.mp (Finset.card_eq_zero.mp hc)
    rwa [hE0, add_zero]
  | succ n ih =>
    intro E hE hc
    classical
    have hne : (toFinsupp E).support.Nonempty := by
      rw [← Finset.card_pos, hc]; exact Nat.succ_pos n
    obtain ⟨p, hp⟩ := hne
    set b : ℤ := toFinsupp E p with hb
    have hb_nonneg : 0 ≤ b := Finsupp.le_def.mp hE p
    set E' : X.CurveDivisor := Finsupp.erase p (toFinsupp E) with hE'
    have hdecomp : CurveDivisor.single p.2 b + E' = E := by
      rw [hE', hb]; exact Finsupp.single_add_erase p (toFinsupp E)
    have hE'nonneg : 0 ≤ E' := by
      rw [hE']
      refine Finsupp.le_def.mpr (fun q => ?_)
      by_cases hq : q = p
      · subst hq; rw [Finsupp.erase_same]; rfl
      · rw [Finsupp.erase_ne hq]; exact Finsupp.le_def.mp hE q
    have hcard : (toFinsupp E').support.card = n := by
      have hEF : toFinsupp E' = Finsupp.erase p (toFinsupp E) := rfl
      rw [hEF, Finsupp.support_erase, Finset.card_erase_of_mem hp, hc, Nat.succ_sub_one]
    have hsingle : CurveDivisor.single p.2 b = b.toNat • CurveDivisor.single p.2 1 := by
      rw [CurveDivisor.nsmul_single_one, Int.toNat_of_nonneg hb_nonneg]
    have hsplit : A + E = (A + E') + b.toNat • CurveDivisor.single p.2 1 := by
      rw [← hdecomp, ← hsingle]; abel
    rw [hsplit]
    exact subsingleton_hModule_one_add_nsmul_single K p.2 (A + E') b.toNat
      (ih E' hE'nonneg hcard)

omit [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 1)] in
/-- **`H¹` vanishing is upward closed** (★): if `H¹(𝒪(D₀)) = 0` and `D₀ ≤ D`, then
`H¹(𝒪(D)) = 0`.  Write `D = D₀ + (D − D₀)` with `D − D₀` effective and peel.

Note the *direction*: this moves a vanishing **up the divisor order**, so it says nothing
about a divisor of large degree that fails to dominate `D₀` — see the module docstring,
item 1.  This is the peel half of `Adelic.coneVanishing_iff_base_and_peel`, discharged on
this carrier; the base half is not supplied here.  Note also that **no finiteness
hypothesis is used**: the statement is about surjections of cohomology modules, not about
their dimensions. -/
theorem subsingleton_hModule_one_of_le {D₀ D : X.CurveDivisor} (hle : D₀ ≤ D)
    (h : Subsingleton (Sheaf.HModule (X.divisorSheaf K D₀) 1)) :
    Subsingleton (Sheaf.HModule (X.divisorSheaf K D) 1) := by
  -- `CurveDivisor` carries only a `PartialOrder` (it is a `def` over `Finsupp`), so
  -- effectivity of the difference is checked coefficientwise rather than by `sub_nonneg`.
  have hE : (0 : X.CurveDivisor) ≤ D - D₀ := by
    refine Finsupp.le_def.mpr (fun q => ?_)
    have hq : (toFinsupp D₀) q ≤ (toFinsupp D) q := Finsupp.le_def.mp hle q
    change (0 : ℤ) ≤ (toFinsupp (D - D₀)) q
    have hsub : (toFinsupp (D - D₀)) q = (toFinsupp D) q - (toFinsupp D₀) q := rfl
    rw [hsub]
    omega
  have hpeel := subsingleton_hModule_one_add_effective K D₀ (D - D₀) hE h
  rwa [add_sub_cancel] at hpeel

end Cone

/-! ## Exact Riemann–Roch on the cone above a vanishing divisor

The ledger gives `χ = h⁰ − h¹`; the peel kills `h¹` above `D₀`.  Together they upgrade the
Riemann *inequality* to an *equality* — but only on the order-cone `{D | D₀ ≤ D}`, never on
a degree half-space.  That distinction is the whole content of the caveat in the module
docstring and is the reason these theorems carry `D₀ ≤ D` rather than `N ≤ deg D`. -/

section ExactRR

/-- **Riemann–Roch as an equality, on the cone above a vanishing divisor** (★):
if `H¹(𝒪(D₀)) = 0` and `D₀ ≤ D`, then `h⁰(𝒪(D)) = χ(𝒪_X) + deg D` exactly.

Not to be read as "Riemann–Roch for large degree": the hypothesis is `D₀ ≤ D` in the
divisor order.  A `D` of huge degree supported away from `D₀` is not covered, and supplying
`D₀` itself is the base problem (module docstring, item 1).

**Provenance.**  The `D₀ ≤ D` form is new here, but its content at a *fixed* vanishing divisor
is AJCR's `RiemannRoch/FLVClass.h0_eq_deg_add_chi_of_subsingleton_hModule_one` — same carrier,
same one-line proof from `Sheaf.chi_eq_h0` and `chi_divisorSheaf`.  This theorem is that plus
the peel, so the only genuinely new part is the `hle` quantifier. -/
theorem h0_divisorSheaf_of_subsingleton_of_le {D₀ D : X.CurveDivisor} (hle : D₀ ≤ D)
    (h : Subsingleton (Sheaf.HModule (X.divisorSheaf K D₀) 1)) :
    (Sheaf.h0 (X.divisorSheaf K D) : ℤ) =
      Sheaf.chi (X.moduleKSheaf K) + CurveDivisor.deg K D := by
  have hvan : Subsingleton (Sheaf.HModule (X.divisorSheaf K D) 1) :=
    subsingleton_hModule_one_of_le K hle h
  have hchi := chi_divisorSheaf K D
  rw [Sheaf.chi_eq_h0 hvan] at hchi
  exact hchi

omit [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 1)] in
/-- **`h¹` vanishes identically above `D₀`**, in the `h¹`-spelling. -/
theorem h1_divisorSheaf_eq_zero_of_le {D₀ D : X.CurveDivisor} (hle : D₀ ≤ D)
    (h : Subsingleton (Sheaf.HModule (X.divisorSheaf K D₀) 1)) :
    Sheaf.h1 (X.divisorSheaf K D) = 0 :=
  Sheaf.h1_eq_zero (subsingleton_hModule_one_of_le K hle h)

/-- **The section drop is exact above `D₀`** (★): once `H¹` has vanished, every further
point adds its full residue degree, `h⁰(𝒪(D)) = h⁰(𝒪(D − x)) + [κ(x) : K]` — the drop
inequality `h0_le_h0_sub_point_add_residueDeg` becomes an equality.  The hypothesis is
vanishing at `D − x`, which the peel then transports to `D`. -/
theorem h0_eq_h0_sub_point_add_residueDeg_of_subsingleton {x : X}
    (hx : x ≠ genericPoint X) (D : X.CurveDivisor)
    (h : Subsingleton (Sheaf.HModule (X.divisorSheaf K (D - CurveDivisor.single hx 1)) 1)) :
    (Sheaf.h0 (X.divisorSheaf K D) : ℤ) =
      Sheaf.h0 (X.divisorSheaf K (D - CurveDivisor.single hx 1)) + X.residueDeg K x := by
  have hvan : Subsingleton (Sheaf.HModule (X.divisorSheaf K D) 1) :=
    subsingleton_hModule_one_of_subsingleton_sub_point K hx D h
  have hstep := chi_step K hx D
  rw [Sheaf.chi_eq_h0 hvan, Sheaf.chi_eq_h0 h] at hstep
  exact hstep

end ExactRR

/-! ## What separates the order-cone from a degree threshold

The adelic lane's `Adelic.exists_bound_subsingleton_h1Mod` concludes vanishing for every
divisor of **weighted degree** `≥ b`, from a base vanishing, a peel datum and the closed
ledger.  On this carrier the peel and the ledger are both theorems, so it is worth recording
exactly what the remaining distance is — and it is *not* bookkeeping.

`Adelic.coneVanishing_iff_base_and_peel` proves, on the adelic carrier, that base-plus-peel
is *equivalent* to vanishing on the whole order-cone `{D' ≥ D₀}`.  There, therefore, the peel
hypothesis is as strong as the conclusion it feeds.

**Be precise about the comparison, because the adelic peel is not wholly open.**
`Adelic.LedgerClosure.peel_pointDivisor_of_notMem_overlap` already discharges the adelic
one-point peel at every prime divisor lying *off* the overlap `U₀ ⊓ U₁`, so the adelic peel's
remaining content is at overlap points — which is most of them, the overlap of a 2-affine
cover of an irreducible curve being dense.  The honest statement of the asymmetry is
therefore: the adelic peel is discharged off the overlap and open on it, while
`subsingleton_hModule_one_of_le` here is unconditional at **every** closed point, because the
dévissage quotient is a skyscraper at each of them and no cover is chosen at all.  The
carrier difference is the absence of a cover, not a difference in proof difficulty.

What no amount of peeling *alone* supplies is the step from the **order**-cone to a **degree**
half-space.  `exists_bound_of_cofinal_vanishing` below isolates that step as a single named
hypothesis: one needs, for each large-degree `D`, *some* divisor `D₀` with `H¹(𝒪(D₀)) = 0` and
`D₀ ≤ D`.  Note why it is not bookkeeping: `deg` is a sum of residue-weighted coefficients, so a
divisor can have huge degree while being small at every point of `supp D₀`.

**AND IT IS PROVED, one import above** (`Ledger/DegreeVanishing.exists_le_subsingleton_of_deg_ge`).
The resolution is that the `D₀` fed to the peel need not be the *given* one: `H¹` vanishing is a
linear-equivalence invariant, so the whole class of `D₀` is available, and the Riemann inequality
picks out a member below `D` as soon as `deg D ≥ deg D₀ + 1 − χ(𝒪_X)`.  An earlier version of
this paragraph asserted that nothing in AJC or AJCR produces the cofinality statement; that was
false, and it was false about ingredients already in this same directory. -/

section DegreeThreshold

/-- **From cofinal vanishing to a degree threshold.**  If above every degree bound the
vanishing locus is *cofinal in the divisor order* — i.e. every `D` of degree `≥ b` dominates
some `D₀` at which `H¹` vanishes — then `H¹(𝒪(D)) = 0` for every such `D`, and Riemann–Roch
is an equality there.

The hypothesis is named so that the obligation is visible: *this theorem* is not a proof of
single-field bounded vanishing, it is a reduction of it to one cofinality statement.  Compare
`Adelic.exists_bound_subsingleton_h1Mod`, which needs a base, a peel and the ledger; here the
peel and the ledger are discharged.

**The hypothesis itself is now a theorem** —
`Ledger/DegreeVanishing.exists_le_subsingleton_of_deg_ge` supplies exactly this `hcof` from one
base vanishing, so `DegreeVanishing.subsingleton_hModule_one_of_deg_ge` *is* the single-field
bounded vanishing this theorem was shaped to receive.  Prefer that statement over instantiating
`hcof` by hand. -/
theorem exists_bound_of_cofinal_vanishing {b : ℤ}
    (hcof : ∀ D : X.CurveDivisor, b ≤ CurveDivisor.deg K D →
      ∃ D₀ : X.CurveDivisor, D₀ ≤ D ∧
        Subsingleton (Sheaf.HModule (X.divisorSheaf K D₀) 1)) :
    ∀ D : X.CurveDivisor, b ≤ CurveDivisor.deg K D →
      (Sheaf.h0 (X.divisorSheaf K D) : ℤ) =
        Sheaf.chi (X.moduleKSheaf K) + CurveDivisor.deg K D := by
  intro D hD
  obtain ⟨D₀, hle, hvan⟩ := hcof D hD
  exact h0_divisorSheaf_of_subsingleton_of_le K hle hvan

omit [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 1)] in
/-- The vanishing half of `exists_bound_of_cofinal_vanishing`, with no finiteness. -/
theorem subsingleton_of_cofinal_vanishing {b : ℤ}
    (hcof : ∀ D : X.CurveDivisor, b ≤ CurveDivisor.deg K D →
      ∃ D₀ : X.CurveDivisor, D₀ ≤ D ∧
        Subsingleton (Sheaf.HModule (X.divisorSheaf K D₀) 1)) :
    ∀ D : X.CurveDivisor, b ≤ CurveDivisor.deg K D →
      Subsingleton (Sheaf.HModule (X.divisorSheaf K D) 1) := by
  intro D hD
  obtain ⟨D₀, hle, hvan⟩ := hcof D hD
  exact subsingleton_hModule_one_of_le K hle hvan

end DegreeThreshold

end Drop

end AlgebraicGeometry
