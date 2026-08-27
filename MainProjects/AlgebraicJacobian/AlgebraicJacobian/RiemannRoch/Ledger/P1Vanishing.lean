/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Adelic.P1ChartData
import AlgebraicJacobian.RiemannRoch.Ledger.VanishingFieldDescent
import AlgebraicJacobian.RiemannRoch.Ledger.NonVacuity

/-!
# `H¹(𝒪_{ℙ¹}) = 0`, `genus ℙ¹ = 0`, and the first *witnessed* `UniformVanishing`

`Ledger/VanishingFieldDescent.lean` (run 0074 r7) produced `UniformBaseDivisor C 0` and
`UniformVanishing C` from `Subsingleton (H¹(𝒪_C))`, and recorded honestly in its own
`§NON-VACUITY` that AJC discharged that hypothesis **at no curve**: a true implication with no
exhibited instance.  Inbox `I-0746` scoped the missing brick as `h¹(𝒪_{ℙ¹}) = 0`.

This file supplies that brick and consumes it.  After this file `UniformVanishing (p1Over k)`
is a theorem with a witness rather than an implication, for every field `k`, with no gate and
no hypothesis at all.

## The mathematics, and where the predecessor's cost estimate was wrong

On the two-chart Laurent cover the Čech cokernel of `𝒪` is
`coker(Γ(V₀) × Γ(V₁) → Γ(V₀ ⊓ V₁)) = coker(k[x] × k[y] → k[x, x⁻¹])` with `xy = 1`, and it
vanishes because `xⁿ` for `n ≥ 0` comes from the `V₀` chart and `x⁻ⁿ = yⁿ` from the `V₁` chart.
Elementary, as `I-0746` said.

**`I-0746`'s prescription was wrong about the obstacle, and re-checking it is what made this
cheap.**  It measured the blocker as structural: `Adelic.LaurentChartData` carries `span_pow_x`
and `span_pow_y` (each *chart* ring is the `k`-span of nonneg powers of its coordinate) but no
field saying the *overlap* is spanned by integer powers, so it recommended either adding a field
— "breaks every `LaurentChartData` constructor in the project" — or proving a
span-of-localization lemma next to `module_finite_H1Cok`.

Neither was needed.  The overlap span is **derivable from the fields already there**, and by the
route the file's own keystone already uses:

* `exists_pow_mul_eq_res` (the extension lemma, already in `Adelic/FinitenessP1.lean`) says every
  `m ∈ Γ(V₀ ⊓ V₁)` has `t ^ n · m` coming from `Γ(V₀)`, `t := x|₀₁` — this *is* the basic-open
  localization `I-0746` wanted, already packaged;
* `span_pow_x` transported along the restriction `Γ(V₀) → Γ(V₀ ⊓ V₁)` puts that element in the
  `k`-span of the nonneg powers of `t` (`mem_span_pow_map_of_span_pow` below — the
  `exists_finset_forall_mem_span_pow_mul` argument with module-finiteness dropped);
* `span_ladder_of_pow_mul_mem_span` (also already there) converts "`t ^ n · m` is in the
  nonneg-power span, for some `n`" into "the two-sided ladder spans", using `t · u = 1`.

So `LaurentChartData.span_ladder_overlap` needs no new field, no new constructor obligation, and
no localization lemma.  Recording this because the mis-pricing, not the mathematics, is what kept
this brick open for a round: the estimate named a structural obstacle that a second look at the
same file dissolved.

## Main statements

* `Adelic.sup_eq_top_of_laurent_pair_span_one` — the abstract core: for `t · u = 1`, a `t`-stable
  `N₀` and a `u`-stable `N₁` both containing `1`, if the ladder over `{1}` spans then
  `N₀ ⊔ N₁ = ⊤`.  Pure algebra, no geometry, no finiteness — the *surjectivity* counterpart of
  `module_finite_quotient_of_laurent_pair`, which gets finiteness from the same data plus
  generators.
* `Adelic.LaurentChartData.span_ladder_overlap` — the overlap ring is the `k`-span of the
  two-sided ladder, derived from the existing fields (see above).
* `Adelic.LaurentChartData.chartSquare` — the datum's own 2-affine cover (the `π = 𝟙` case of
  `pullbackSquare`, stated without a morphism so it needs no `IsFinite`).
* `Adelic.LaurentChartData.subsingleton_h1Cok` — **`Ȟ¹(𝒪) = 0` on that cover**, for *any*
  `Spec k`-scheme carrying Laurent chart data.  No properness, no smoothness, no curve binder.
* `Adelic.subsingleton_hModule_one_p1Over` — the same on the genus carrier at `ℙ¹_k`.
* `Adelic.genus_p1Over_eq_zero` — **`genus ℙ¹_k = 0`**, every field.
* `Adelic.uniformVanishing_p1Over`, `Adelic.uniformBaseDivisor_p1Over` — r7's producers with
  their hypothesis discharged: extension-uniform bounded vanishing **at a curve AJC has**.

## SCOPE: this is genus 0 and it does not touch the other two cluster-P gaps

The three statements the task keeps apart stay apart, and this file moves exactly one of them
from "implication" to "instance" — at the degenerate curve.

1. **Single-field vanishing: closed at `ℙ¹`, and only there.**  `subsingleton_h1Cok` is general
   in the *datum*, but a `LaurentChartData` is the two-chart structure of a rational curve; AJC
   exhibits one such datum (`p1LaurentChartData`).  For `genus C ≥ 1` there is no datum and this
   file says nothing.
2. **Extension-uniformity: witnessed at `ℙ¹`, still open in general.**  `uniformVanishing_p1Over`
   is r7's implication with the antecedent supplied, so extension-uniformity is now known to be
   *non-vacuous* as a type.  The general case is unchanged: it still needs
   `UniformBaseDivisor C d` for `d > 0`, which needs the general-module base-change comparison
   AJC does not have (r7 measured that ceiling; nothing here moves it).
3. **Global generation: untouched.**  Cluster-P item 3 is a single-field statement about `H⁰` and
   generation at a point; nothing here is about `H⁰` or about a divisor sheaf with `D ≠ 0`.

What this DOES settle is the non-vacuity question `VanishingFieldDescent`'s `§NON-VACUITY` left
open, and only that: the genus-0 branch of cluster P now has a curve in it.

## Provenance

**Rederived in AJC's abstractions.**  Every input is AJC's own and was already in
`Adelic/FinitenessP1.lean` (`exists_pow_mul_eq_res`, `span_ladder_of_pow_mul_mem_span`,
`pow_mul_mem`, the `LaurentChartData` fields) or `Adelic/P1ChartData.lean`
(`p1LaurentChartData`); the crossing to the genus carrier is `hModuleOneEquivH1Cok_curve`
(gate-free, every cover, every field).  Not a port: AJCR's nearest statement
(`WindowFieldTransport.subsingleton_h1_windowN`) is about a window divisor on its glued-datum
carrier, and r7 measured that boundary as unbridged in both directions.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Adelic

/-! ## §1. The abstract surjectivity core

`module_finite_quotient_of_laurent_pair` gets *finiteness* of `M ⧸ (N₀ ⊔ N₁)` from a Laurent pair
plus finitely many generators.  With the generator set taken to be `{1}` the same data gives the
stronger conclusion that the quotient is *zero* — the two lattices already exhaust `M`.  Stated
separately rather than as a corollary because the finiteness proof's middle band is exactly what
is empty here. -/

section AbstractCore

variable {k : Type*} [Field k] {M : Type*} [CommRing M] [Algebra k M]

/-- **The two chart lattices exhaust `M`** when each contains `1` and the two-sided ladder over
`{1}` spans: `N₀ ⊔ N₁ = ⊤`.

Pure algebra: `t · u = 1`, `N₀` stable under `t`, `N₁` under `u`, both containing `1`.  Every
rung `t ^ j` of the positive half lies in `N₀` (iterated stability, `pow_mul_mem`), every rung
`u ^ j` of the negative half in `N₁`, and the spanning hypothesis says those rungs generate. -/
theorem sup_eq_top_of_laurent_pair_span_one {t u : M} {N₀ N₁ : Submodule k M}
    (h₀ : ∀ a ∈ N₀, t * a ∈ N₀) (h₁ : ∀ a ∈ N₁, u * a ∈ N₁)
    (h1₀ : (1 : M) ∈ N₀) (h1₁ : (1 : M) ∈ N₁)
    (hspan : ⊤ ≤ Submodule.span k
      ((⋃ j : ℕ, (fun z => t ^ j * z) '' ({1} : Set M))
        ∪ (⋃ j : ℕ, (fun z => u ^ j * z) '' ({1} : Set M)))) :
    N₀ ⊔ N₁ = ⊤ := by
  refine le_antisymm le_top ?_
  refine le_trans hspan (Submodule.span_le.mpr ?_)
  rintro z (hz | hz)
  · simp only [Set.mem_iUnion, Set.mem_image, Set.mem_singleton_iff] at hz
    obtain ⟨j, _, rfl, rfl⟩ := hz
    exact Submodule.mem_sup_left (by simpa using pow_mul_mem h₀ j h1₀)
  · simp only [Set.mem_iUnion, Set.mem_image, Set.mem_singleton_iff] at hz
    obtain ⟨j, _, rfl, rfl⟩ := hz
    exact Submodule.mem_sup_right (by simpa using pow_mul_mem h₁ j h1₁)

/-- **Span transport along a `k`-algebra map.**  If `R` is the `k`-span of the powers of `x`,
every element of the image of `φ : R →+* A` lies in the `k`-span of the powers of `φ x`.

This is the `smul` case of `exists_finset_forall_mem_span_pow_mul`'s induction with the
module-finiteness input dropped; extracted because the overlap span below needs exactly this and
none of the generator bookkeeping. -/
theorem mem_span_pow_map_of_span_pow {R A : Type*} [CommRing R] [CommRing A]
    [Algebra k R] [Algebra k A] {φ : R →+* A}
    (hφ : ∀ c : k, φ (algebraMap k R c) = algebraMap k A c) {x : R}
    (hx : ⊤ ≤ Submodule.span k (Set.range fun n : ℕ => x ^ n)) (r : R) :
    φ r ∈ Submodule.span k (Set.range fun n : ℕ => φ x ^ n) := by
  let φₗ : R →ₗ[k] A :=
    { toFun := φ
      map_add' := φ.map_add
      map_smul' := fun c r => by
        simp only [Algebra.smul_def, map_mul, hφ, RingHom.id_apply] }
  have h1 : φ r ∈ Submodule.map φₗ (Submodule.span k (Set.range fun n : ℕ => x ^ n)) :=
    Submodule.mem_map_of_mem (hx trivial)
  rw [Submodule.map_span] at h1
  refine Submodule.span_le.mpr ?_ h1
  rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
  exact Submodule.subset_span ⟨n, (map_pow φ x n).symm⟩

end AbstractCore

/-! ## §2. The overlap ring of a Laurent chart datum is the Laurent ring

The step `I-0746` priced as a new structure field.  It is derivable; see the module docstring for
why the estimate was wrong and which three existing lemmas do the work. -/

section OverlapSpan

variable {k : Type u} [Field k] {Y : Over (Spec (CommRingCat.of k))}

/-- **The overlap ring is spanned by the two-sided ladder** (★): `Γ(V₀ ⊓ V₁)` is the `k`-span of
`{t ^ j} ∪ {u ^ j}` for `t = x|₀₁`, `u = y|₀₁` — the span form of `Γ(V₀ ⊓ V₁) = k[x, x⁻¹]`.

Derived from the `LaurentChartData` fields already present (`span_pow_x`, `inf_eq_basicOpen_x`,
`res_x_mul_res_y`, `isAffineOpen_V₀`), with no new field and no new constructor obligation. -/
theorem LaurentChartData.span_ladder_overlap (D : LaurentChartData Y) :
    ⊤ ≤ Submodule.span k
      ((⋃ j : ℕ, (fun z => (Y.left.presheaf.map (homOfLE
            (inf_le_left : D.V₀ ⊓ D.V₁ ≤ D.V₀)).op).hom D.x ^ j * z) ''
              ({1} : Set Γ(Y.left, D.V₀ ⊓ D.V₁)))
        ∪ (⋃ j : ℕ, (fun z => (Y.left.presheaf.map (homOfLE
            (inf_le_right : D.V₀ ⊓ D.V₁ ≤ D.V₁)).op).hom D.y ^ j * z) ''
              ({1} : Set Γ(Y.left, D.V₀ ⊓ D.V₁)))) := by
  refine span_ladder_of_pow_mul_mem_span D.res_x_mul_res_y _ ?_
  intro m
  -- the extension lemma: `t ^ n · m` is the restriction of a chart section
  obtain ⟨n, a, ha⟩ := exists_pow_mul_eq_res D.isAffineOpen_V₀ D.x D.inf_eq_basicOpen_x
    inf_le_left m
  refine ⟨n, ?_⟩
  rw [ha]
  -- and the chart span transports along the restriction, which is a `k`-algebra map
  have hmem : (Y.left.presheaf.map (homOfLE (inf_le_left : D.V₀ ⊓ D.V₁ ≤ D.V₀)).op).hom a
      ∈ Submodule.span k (Set.range fun j : ℕ =>
        (Y.left.presheaf.map (homOfLE (inf_le_left : D.V₀ ⊓ D.V₁ ≤ D.V₀)).op).hom D.x ^ j) :=
    mem_span_pow_map_of_span_pow
      (φ := (Y.left.presheaf.map (homOfLE (inf_le_left : D.V₀ ⊓ D.V₁ ≤ D.V₀)).op).hom)
      (fun c => Scheme.toModuleKSheaf.algebraMap_naturality (C := Y)
        (homOfLE (inf_le_left : D.V₀ ⊓ D.V₁ ≤ D.V₀)).op c)
      D.span_pow_x a
  refine Submodule.span_le.mpr ?_ hmem
  rintro _ ⟨j, rfl⟩
  exact Submodule.subset_span (Set.mem_iUnion.mpr ⟨j, ⟨1, rfl, by simp⟩⟩)

/-! ## §3. `Ȟ¹(𝒪) = 0` on the chart cover of the datum -/

/-- **The datum's own 2-affine cover.**  The `π = 𝟙` case of `LaurentChartData.pullbackSquare`,
stated without a morphism so that it carries no `IsFinite` binder (the identity is finite, but a
statement about `Y` should not have to mention a map to `Y`).

Not a duplicate of `Adelic.p1CoverSquare` (`Adelic/FinitenessP1.lean`), which is built directly on
the concrete `ℙ(ULift (Fin 2); Spec k)`: this one is generic in the *datum*, which is what lets
§3's vanishing be stated for any `Y` carrying one.  Checked rather than assumed: the two are
*not* defined in terms of each other — `p1CoverSquare`
and `p1LaurentChartData` independently take their opens from the same `p1Chart`/
`isAffineOpen_p1Chart`/`p1Chart_sup_eq_top` lemmas, and the `isAffineOpen_inf` field is proved
differently on each side (`isAffineOpen_p1Chart_inf` there, via `inf_eq_basicOpen_x` here).  So at
`ℙ¹` they agree on `U₁`, `U₂` and `cover` by having the same definitions plugged in, not by one
delegating to the other.  Nothing downstream has to choose: the §4 statements go through
`chartSquare` because `subsingleton_h1Cok` is stated at it. -/
noncomputable def LaurentChartData.chartSquare (D : LaurentChartData Y) :
    Y.left.AffineCoverMVSquare where
  U₁ := D.V₀
  U₂ := D.V₁
  isAffineOpen_U₁ := D.isAffineOpen_V₀
  isAffineOpen_U₂ := D.isAffineOpen_V₁
  isAffineOpen_inf := by
    rw [D.inf_eq_basicOpen_x]
    exact D.isAffineOpen_V₀.basicOpen D.x
  cover := D.cover

/-- **`Ȟ¹(𝒪) = 0` on the chart cover of a Laurent chart datum** (★★).

The Čech cokernel is `Γ(V₀ ⊓ V₁) ⧸ (Γ(V₀) + Γ(V₁))`, and §2 plus §1 say the two chart images
already fill the overlap: the positive powers of the coordinate come from `V₀`, the negative ones
from `V₁`, and by `span_ladder_overlap` those span everything.

**No curve hypothesis of any kind** — no properness, no smoothness, no irreducibility, no
finiteness of cohomology.  All that is used is the datum. -/
theorem LaurentChartData.subsingleton_h1Cok (D : LaurentChartData Y) :
    Subsingleton (D.chartSquare.H1Cok (Scheme.toModuleKSheaf Y)) := by
  classical
  set σ₀ : Γ(Y.left, D.V₀) →ₗ[k] Γ(Y.left, D.V₀ ⊓ D.V₁) :=
    Scheme.sectionRestrict (Scheme.toModuleKSheaf Y) (inf_le_left : D.V₀ ⊓ D.V₁ ≤ D.V₀) with hσ₀
  set σ₁ : Γ(Y.left, D.V₁) →ₗ[k] Γ(Y.left, D.V₀ ⊓ D.V₁) :=
    Scheme.sectionRestrict (Scheme.toModuleKSheaf Y) (inf_le_right : D.V₀ ⊓ D.V₁ ≤ D.V₁) with hσ₁
  have hσ₀app : ∀ a, σ₀ a = (Y.left.presheaf.map (homOfLE
      (inf_le_left : D.V₀ ⊓ D.V₁ ≤ D.V₀)).op).hom a := fun _ => rfl
  have hσ₁app : ∀ a, σ₁ a = (Y.left.presheaf.map (homOfLE
      (inf_le_right : D.V₀ ⊓ D.V₁ ≤ D.V₁)).op).hom a := fun _ => rfl
  -- the two lattices: `t`-stable, `u`-stable, both containing `1`
  have h₀ : ∀ a ∈ LinearMap.range σ₀, (σ₀ D.x) * a ∈ LinearMap.range σ₀ := by
    rintro _ ⟨b, rfl⟩
    exact ⟨D.x * b, by simp only [hσ₀app, map_mul]⟩
  have h₁ : ∀ a ∈ LinearMap.range σ₁, (σ₁ D.y) * a ∈ LinearMap.range σ₁ := by
    rintro _ ⟨b, rfl⟩
    exact ⟨D.y * b, by simp only [hσ₁app, map_mul]⟩
  have h1₀ : (1 : Γ(Y.left, D.V₀ ⊓ D.V₁)) ∈ LinearMap.range σ₀ :=
    ⟨1, by rw [hσ₀app]; exact map_one _⟩
  have h1₁ : (1 : Γ(Y.left, D.V₀ ⊓ D.V₁)) ∈ LinearMap.range σ₁ :=
    ⟨1, by rw [hσ₁app]; exact map_one _⟩
  have hsupN : LinearMap.range σ₀ ⊔ LinearMap.range σ₁ = ⊤ :=
    sup_eq_top_of_laurent_pair_span_one h₀ h₁ h1₀ h1₁ D.span_ladder_overlap
  -- the Čech difference map has that sum as its range
  -- (`le_trans` rather than `rw`: the `Scheme.Opens`/`Opens Y.toTopCat` presentation diamond
  -- makes the motive check of a rewrite at `⊤` fail here)
  have hsup : LinearMap.range (D.chartSquare.sectionDiff (Scheme.toModuleKSheaf Y)) = ⊤ := by
    refine le_antisymm le_top (le_trans (le_of_eq hsupN.symm) ?_)
    refine sup_le ?_ ?_
    · rintro _ ⟨a, rfl⟩
      exact ⟨(a, 0), by
        change σ₀ a - σ₁ 0 = σ₀ a
        rw [map_zero, sub_zero]⟩
    · rintro _ ⟨b, rfl⟩
      refine ⟨(0, -b), ?_⟩
      change σ₀ 0 - σ₁ (-b) = σ₁ b
      rw [map_zero, map_neg, zero_sub, neg_neg]
  rw [Scheme.AffineCoverMVSquare.H1Cok, hsup]
  infer_instance

end OverlapSpan

/-! ## §4. At `ℙ¹`: the genus, and r7's producers with their hypothesis discharged -/

section P1

variable (k : Type u) [Field k]

/-- **`H¹(ℙ¹_k, 𝒪) = 0`** (★★), on this project's genus carrier
`Scheme.HModule k (toModuleKSheaf (p1Over k)) 1`.

§3 at the concrete datum `p1LaurentChartData`, crossed to the derived carrier by the gate-free
comparison `hModuleOneEquivH1Cok_curve` (every 2-affine cover, every field).

This is the statement `Ledger/VanishingFieldDescent.lean`'s `§NON-VACUITY` recorded as **absent
from AJC**, and `I-0746` scoped as the missing brick.

Re-checked rather than inherited, since that absence claim is what makes this file worth landing.
One other declaration in AJC concludes `genus C = 0`: `Pic0.genus_eq_zero_of_homogeneous`
(`Picard/HomogeneityOrbitCollapse.lean`).  It is **not** a competing witness and does not weaken
the claim — it is a *no-go*, deriving `genus C = 0` from four heavy hypotheses (including the
sorried `HasPicScheme`) in order to show they are inconsistent with positive genus.  It exhibits
no curve.  This file is the first declaration in AJC that concludes vanishing, or genus zero, at a
*named object*. -/
theorem subsingleton_hModule_one_p1Over :
    Subsingleton (Scheme.HModule k (Scheme.toModuleKSheaf (p1Over k)) 1) :=
  ((p1LaurentChartData k).chartSquare.hModuleOneEquivH1Cok_curve).toEquiv.subsingleton_congr.mpr
    (p1LaurentChartData k).subsingleton_h1Cok

/-- **`genus ℙ¹_k = 0`**, for every field `k` (★★).

`Subsingleton` first, `finrank` after — the direction that matters, since `finrank` reads `0` on
an infinite-dimensional space and so a genus computation alone would not have given the vanishing
(the standing distinction of `Ledger/VanishingFieldDescent.lean` §2).  Here the vanishing is the
theorem and the genus is its corollary. -/
theorem genus_p1Over_eq_zero : genus (p1Over k) = 0 := by
  haveI := subsingleton_hModule_one_p1Over k
  change Module.finrank k (Scheme.HModule k (Scheme.toModuleKSheaf (p1Over k)) 1) = 0
  exact Module.finrank_zero_of_subsingleton

/-- **`UniformBaseDivisor (ℙ¹_k) 0`** (★★) — r7's producer with its hypothesis discharged.

`VanishingFieldDescent.uniformBaseDivisor_zero_of_genus_eq_zero` applied at `genus ℙ¹ = 0`. -/
theorem uniformBaseDivisor_p1Over : UniformBaseDivisor (p1Over k) 0 :=
  uniformBaseDivisor_zero_of_genus_eq_zero (p1Over k) (genus_p1Over_eq_zero k)

/-- **Extension-uniform bounded vanishing holds at `ℙ¹_k`** (★★★) — the first `UniformVanishing`
in AJC **with an exhibited witness**.

`VanishingFieldDescent.uniformVanishing_of_genus_eq_zero` was a true implication whose antecedent
AJC discharged at no curve; `genus_p1Over_eq_zero` discharges it.  So `UniformVanishing` is now
known to be a non-vacuous property: one threshold `b = 0 + genus = 0`, serving every extension
`κ/k` — finite, infinite, inseparable, `k̄` — simultaneously.

**Genus 0 is the whole content, and the general case is not affected.**  The threshold is `0`
because the curve is rational; for `genus C ≥ 1` this file supplies nothing, and the residue
there is unchanged: `UniformBaseDivisor C d` for `d > 0`, which needs a divisor-level base-change
comparison AJC does not have.  See §SCOPE of the module docstring. -/
theorem uniformVanishing_p1Over : UniformVanishing (p1Over k) :=
  uniformVanishing_of_genus_eq_zero (p1Over k) (genus_p1Over_eq_zero k)

end P1

end AlgebraicGeometry.Adelic
