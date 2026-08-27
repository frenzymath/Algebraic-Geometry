/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Albanese.GrpObjFoldSum

/-!
# The symmetric power as an *interface*, and the two maps it produces

Milne's proof of the Albanese universal property (*Abelian Varieties* III.6
Proposition 6.1) uses the `n`-th symmetric power `Sym^n C` only through its
**universal property**: every `S_n`-symmetric morphism `C^n ⟶ T` factors uniquely
through the symmetrisation projection `π : C^n ⟶ Sym^n C`.

At this Mathlib pin the *object* `Sym^n C` does not exist for a proper curve — there is no
quotient of a scheme by a finite group action, and mathlib's `SymmetricPower` is for
modules. (The `analogies/m3-route-audit.md` figure of 2400–3800 lines priced Milne's
affine-and-glue route; `Albanese/SymPowColimit.lean` later reduced the obligation to one
`HasColimit` instance and discharged the affine half outright. Read that file before
budgeting anything from this paragraph.) Writing `Sym^n C := sorry` makes every downstream
equation a statement
about a junk term, which is why `Albanese/AlbaneseUP.lean` keeps its obligations
unproved rather than discharging them against a meaningless definition.

This file takes the other route: it **names the interface** as a structure
`SymPowData C n`, and then proves, unconditionally, everything Milne's argument
derives from it. The missing geometry is isolated in exactly one place — inhabiting
`SymPowData` — and nothing downstream is a statement about `sorry`.

## What is proved here (no `sorry`, nothing conditional on unproved statements)

* `SymPowData.symAVMap` — Milne's `Sym^n φ`. Given `φ : C ⟶ A` into a *commutative*
  monoid object, the `n`-fold sum `powSum n φ` is `S_n`-symmetric
  (`MonObj.powSum_perm`, already proved), so the interface descends it. This is the
  content of `lem:symmetric_product_av_map`, and it is a construction, not a
  hypothesis.
* `SymPowData.proj_comp_symAVMap` / `SymPowData.symAVMap_unique` — its defining
  equation and uniqueness.
* `MonObj.basePointShift` — the morphism `Q ↦ (P₀, …, Q, …, P₀)` placing `Q` in a
  designated slot `i₀` and the basepoint elsewhere. Milne's `Q ↦ Q + (n−1) P₀`
  factors through it.
* `MonObj.basePointShift_comp_powSum` — **the computation that makes the backward
  direction of the Albanese connector work**: for a *pointed* `φ` (`P₀ ≫ φ = η[A]`),

  `basePointShift P₀ i₀ ≫ powSum n φ = φ`,

  because `φ(Q) + φ(P₀) + ⋯ + φ(P₀) = φ(Q) + η + ⋯ + η = φ(Q)`. In the hom-monoid
  this is `Finset.prod_ite_eq`; the geometry evaporates exactly as it does in
  `GrpObjFoldSum.lean`.
* `symPowDataOne` and `symPowDataOne_proj_perm` — **an inhabitant of the interface
  *together with* the symmetry hypothesis**: `Sym^1 C = C`. See the warning below for
  why both halves are needed and what they do and do not show.

## What non-vacuity does and does not mean here — read this before citing it

`SymPowData C n` **on its own is trivially inhabited for every `n`** — and the witness
is recorded below as `symPowDataTrivial` rather than left as a remark, so that nobody
has to rediscover it:

```
carrier := C^n,  proj := 𝟙,  desc := fun h _ => ⟨h, Category.id_comp h, …⟩
```

With `proj = 𝟙` the universal property degenerates to `∃! u, 𝟙 ≫ u = h`. So the bare
structure is nearly free, and exhibiting *some* `SymPowData` proves nothing.

What the downstream theorems actually quantify over is the **pair**
`(D, hproj)`, where `hproj : ∀ σ, permAut C σ ≫ D.proj = D.proj` says the projection
is genuinely symmetric. The `proj := 𝟙` trick fails that whenever `permAut C σ ≠ 𝟙`, which
for `n ≥ 2` holds as soon as `C` has two distinct global points — the case of interest, and
proved in `Albanese/SymPowColimit.lean` (`permAut_swap_ne_id_of_points`). It is *not*
automatic from `n ≥ 2` alone: at a **terminal** `C` the trivial datum does satisfy `hproj`
at every `n` (`permAut_eq_id_of_isTerminal`), so an unqualified "fails for `n ≥ 2`" is
false. So the pair is the meaningful object away from that degenerate case, and this file
witnesses it for `n = 1`: `symPowDataOne` plus `symPowDataOne_proj_perm`.

Two honest caveats about that witness:

* `n = 1` is the case where the *interesting* step degenerates. The forward direction
  of the connector (`Albanese/AlbaneseFromData.lean`) uses that `ψ` is a homomorphism
  to move it through a `g`-fold product; a 1-fold product has one factor, so at
  `n = 1` that step is mere associativity. The general-`n` theorem is the real one —
  do not cite `n = 1` as evidence that the group law is exercised.
* Consequently, "the interface is inhabited" should be read as *the hypotheses are
  consistent and the statements are not about nothing*, not as *the hard case is
  covered*.

## What is *not* here — but see `Albanese/SymPowColimit.lean` first

**This section is superseded in part (2026-07-28).** It said `SymPowData C n` for `n ≥ 2`
is "the missing quotient", the honest boundary of the leg. That reading was tied to one
presentation of the object — Milne's affine-and-glue construction — and
`Albanese/SymPowColimit.lean` replaces it:

* the pair `(D, hproj)` **is** a colimit of the `S_n`-action on `C^n`, in both directions
  (`symPowOfColimit`, `SymPowData.isColimit`, and `hasColimit_permDiagram_iff` for the
  equivalence, so the identification loses nothing);
* consequently `hproj` — the half that only `n = 1` witnessed here — is `colimit.w`, free
  at every `n`;
* and the **affine algebra** case is *inhabited* at every `n`
  (`symPowData_affineAlgebra`, in `(Under k)ᵒᵖ`), with no construction written. Note the
  careful wording: that is the inhabitation statement, not a formalisation of Milne III.3
  Proposition 3.1's affine half — identifying the carrier as `Spec (A^{⊗n})^{S_n}` is
  expected but **not proved**. See that file's §5 header.

What is genuinely still missing is the **gluing**, as `HasColimit (permDiagram C n)` for the
curve at hand. So the boundary moved from a construction subproject to one instance about
one named diagram. (State it per-diagram, not as `HasColimitsOfShape … Scheme`: the
quantified form is strictly stronger and believed false at this pin.)

Also note the warning above is now *checked* rather than asserted: `permAut_swap_ne_id`
exhibits `permAut ≠ 𝟙` at a transposition (in `Type`, at `Bool`, `n = 2`), so
`symPowDataTrivial` demonstrably fails `hproj`. Nothing in this tree had verified that.

See `Albanese/AlbaneseFromData.lean` for the Albanese universal property proved over this
interface, `Albanese/AlbaneseFromColimit.lean` for the same statement with no `SymPowData`
argument at all, and the header of `Albanese/AlbaneseUP.lean` for the pinned statements.

## References

Milne, *Abelian Varieties*, §III.3 Proposition 3.1 (the symmetric power) and §III.6
Proposition 6.1, p. 104; blueprint `def:symmetric_power_curve` and
`lem:symmetric_product_av_map` in `blueprint/src/chapters/Albanese_AlbaneseUP.tex`.
-/

set_option autoImplicit false

universe v u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace CategoryTheory

variable {K : Type u} [Category.{v} K] [CartesianMonoidalCategory K] [HasFiniteProducts K]

/-! ## §1. The interface

`SymPowData C n` is exactly the data Milne's proof uses: a scheme, a symmetrisation
projection from `C^n`, and the universal property for `S_n`-symmetric morphisms. The
symmetry hypothesis is phrased with `MonObj.permAut` (`Albanese/GrpObjFoldSum.lean`),
the factor-permuting automorphism of `C^n`. -/

/-- **The universal property of the `n`-th symmetric power, as data.**

A `SymPowData C n` is a `carrier` (morally `Sym^n C`) together with a symmetrisation
morphism `proj : C^n ⟶ carrier` through which *every* `S_n`-symmetric morphism out of
`C^n` factors uniquely.

This is the interface, not the construction: see `symPowDataOne` for the case `n = 1`,
and the module header for why the general case is a separate subproject. -/
structure SymPowData (C : K) (n : ℕ) where
  /-- The underlying object, morally `Sym^n C`. -/
  carrier : K
  /-- The symmetrisation projection `π : C^n ⟶ Sym^n C`. -/
  proj : (∏ᶜ (fun _ : Fin n => C)) ⟶ carrier
  /-- **The universal property.** Every `S_n`-symmetric morphism `C^n ⟶ T` factors
  uniquely through `proj`. -/
  desc : ∀ {T : K} (h : (∏ᶜ (fun _ : Fin n => C)) ⟶ T),
    (∀ σ : Equiv.Perm (Fin n), MonObj.permAut C σ ≫ h = h) →
    ∃! u : carrier ⟶ T, proj ≫ u = h

namespace SymPowData

variable {C : K} {n : ℕ}

omit [CartesianMonoidalCategory K] in
/-- Uniqueness of a factorisation through `proj`, in the form used at call sites:
two morphisms out of the carrier that agree after `proj` are equal.

Note that no symmetry hypothesis is needed: if `u₁` and `u₂` both factor `h` then
`h` *is* symmetric (being `proj ≫ u₁` with `proj` symmetric would be the argument,
but here we get it more cheaply — apply `desc` to `proj ≫ u₁`, whose symmetry follows
from that of `proj` composed with anything). We therefore take the symmetry of
`proj` itself as the input. -/
theorem hom_ext_of_proj (D : SymPowData C n) {T : K} {u₁ u₂ : D.carrier ⟶ T}
    (hproj : ∀ σ : Equiv.Perm (Fin n), MonObj.permAut C σ ≫ D.proj = D.proj)
    (h : D.proj ≫ u₁ = D.proj ≫ u₂) : u₁ = u₂ := by
  obtain ⟨u, -, huniq⟩ := D.desc (D.proj ≫ u₁) (fun σ => by rw [← Category.assoc, hproj])
  rw [huniq u₁ rfl, huniq u₂ h.symm]

section SymAVMap

variable [BraidedCategory K]

/-- **Milne's `Sym^n φ`.** For `φ : C ⟶ A` into a commutative monoid object, the
`n`-fold sum `(P₁,…,P_n) ↦ φ(P₁) + ⋯ + φ(P_n)` is `S_n`-symmetric
(`MonObj.powSum_perm` — Milne's "clearly this is symmetric"), so the interface
descends it to `Sym^n C ⟶ A`.

This is `lem:symmetric_product_av_map`: a *construction* from the interface, with no
further geometric input. -/
noncomputable def symAVMap {A : K} [MonObj A] [IsCommMonObj A]
    (D : SymPowData C n) (φ : C ⟶ A) : D.carrier ⟶ A :=
  (D.desc (MonObj.powSum n φ) (fun σ => MonObj.powSum_perm n φ σ)).choose

/-- The defining equation of `Sym^n φ`: it restores the `n`-fold sum along `proj`. -/
@[reassoc]
theorem proj_comp_symAVMap {A : K} [MonObj A] [IsCommMonObj A]
    (D : SymPowData C n) (φ : C ⟶ A) :
    D.proj ≫ D.symAVMap φ = MonObj.powSum n φ :=
  (D.desc (MonObj.powSum n φ) (fun σ => MonObj.powSum_perm n φ σ)).choose_spec.1

/-- `Sym^n φ` is the *unique* morphism restoring the `n`-fold sum along `proj`. -/
theorem symAVMap_unique {A : K} [MonObj A] [IsCommMonObj A]
    (D : SymPowData C n) (φ : C ⟶ A) (u : D.carrier ⟶ A)
    (hu : D.proj ≫ u = MonObj.powSum n φ) : u = D.symAVMap φ :=
  (D.desc (MonObj.powSum n φ) (fun σ => MonObj.powSum_perm n φ σ)).choose_spec.2 u hu

end SymAVMap

end SymPowData

/-! ## §2. Milne's `Q ↦ Q + (n − 1) P₀`, and why it collapses the sum

The backward direction of the Albanese connector restricts the symmetric-power
equation along `Q ↦ (Q, P₀, …, P₀)`. The whole force of that step is the following
computation in the hom-monoid: summing `φ` over such a tuple gives
`φ(Q) + φ(P₀) + ⋯ + φ(P₀)`, and a *pointed* `φ` kills every term but the first. -/

namespace MonObj

variable {C : K}

/-- **The basepoint shift `Q ↦ (P₀, …, Q, …, P₀)`**, placing `Q` in the designated
slot `i₀` and the basepoint `P₀ : 𝟙_ ⟶ C` in every other slot.

Composed with the symmetrisation projection this is Milne's
`Q ↦ Q + (n − 1) P₀ : C ⟶ Sym^n C`. -/
noncomputable def basePointShift (P0 : 𝟙_ K ⟶ C) {n : ℕ} (i₀ : Fin n) :
    C ⟶ (∏ᶜ (fun _ : Fin n => C)) :=
  Pi.lift (fun i => if i = i₀ then 𝟙 C else toUnit C ≫ P0)

@[reassoc (attr := simp)]
theorem basePointShift_π (P0 : 𝟙_ K ⟶ C) {n : ℕ} (i₀ i : Fin n) :
    basePointShift P0 i₀ ≫ Pi.π (fun _ : Fin n => C) i
      = if i = i₀ then 𝟙 C else toUnit C ≫ P0 := by
  simp only [basePointShift, Pi.lift_π]

section Collapse

variable [BraidedCategory K]

/-- **The collapse computation.** For `φ : C ⟶ A` into a commutative monoid object
which is *pointed* at `P₀` (`P₀ ≫ φ = η[A]`), summing `φ` over the tuple
`(P₀, …, Q, …, P₀)` returns `φ` itself:

`basePointShift P₀ i₀ ≫ powSum n φ = φ`.

Every slot other than `i₀` contributes `toUnit ≫ P₀ ≫ φ = toUnit ≫ η[A] = 1`, the
identity of the hom-monoid, so the product collapses to the single factor at `i₀`
(`Finset.prod_ite_eq`). This is the entire content of Milne's "restrict along
`Q ↦ Q + (g − 1) P₀` and use `φ(P₀) = η_A`". -/
theorem basePointShift_comp_powSum {A : K} [MonObj A] [IsCommMonObj A]
    (P0 : 𝟙_ K ⟶ C) {n : ℕ} (i₀ : Fin n) (φ : C ⟶ A) (hφ : P0 ≫ φ = η[A]) :
    basePointShift P0 i₀ ≫ powSum n φ = φ := by
  classical
  rw [comp_powSum]
  have hterm : ∀ i : Fin n,
      basePointShift P0 i₀ ≫ Pi.π (fun _ : Fin n => C) i ≫ φ
        = if i₀ = i then φ else 1 := by
    intro i
    rw [← Category.assoc, basePointShift_π]
    by_cases h : i = i₀
    · subst h; simp
    · rw [if_neg h, if_neg (fun hc => h hc.symm), Category.assoc, hφ, ← Hom.one_def]
  rw [Finset.prod_congr rfl (fun i _ => hterm i), Finset.prod_ite_eq]
  simp

end Collapse

end MonObj

/-! ## §3. The interface is inhabited: `Sym^1 C = C`

For `n = 1` the symmetric group is trivial, `C^1 ⟶ C` is an isomorphism, and the
universal property is immediate. Both halves of the meaningful object are supplied: the
datum `symPowDataOne` and the symmetry `symPowDataOne_proj_perm`.

As the module header warns, the bare structure `SymPowData C n` is trivially inhabited
for every `n` (take `proj := 𝟙`), so it is the **pair** with `hproj` that carries
content — and `n = 1` is the degenerate case for the group-law step. See the header. -/

/-- **`Sym^1 C = C`.** The unique projection `C^1 ⟶ C` is an isomorphism, so every
morphism out of `C^1` — symmetric or not, since `S_1` is trivial — factors uniquely
through it.

For `n ≥ 2`, inhabiting `SymPowData` *together with the symmetry hypothesis* is equivalent
to a colimit of the `S_n`-action (`Albanese/SymPowColimit.lean`) — proved for affine
`k`-schemes at every `n`, still open for a proper curve. -/
noncomputable def symPowDataOne (C : K) : SymPowData C 1 where
  carrier := C
  proj := Pi.π (fun _ : Fin 1 => C) 0
  desc := fun {T} h _ => by
    -- `Pi.lift (fun _ => 𝟙 C)` is a two-sided inverse of the single projection.
    have hsec : Pi.lift (fun _ : Fin 1 => (𝟙 C)) ≫ Pi.π (fun _ : Fin 1 => C) 0 = 𝟙 C := by
      rw [Pi.lift_π]
    have hret : Pi.π (fun _ : Fin 1 => C) 0 ≫ Pi.lift (fun _ : Fin 1 => (𝟙 C))
        = 𝟙 (∏ᶜ (fun _ : Fin 1 => C)) := by
      apply Pi.hom_ext
      intro b
      have hb : b = 0 := Subsingleton.elim _ _
      subst hb
      rw [Category.assoc, Pi.lift_π, Category.comp_id, Category.id_comp]
    refine ⟨Pi.lift (fun _ : Fin 1 => (𝟙 C)) ≫ h, ?_, ?_⟩
    · change Pi.π (fun _ : Fin 1 => C) 0 ≫ Pi.lift (fun _ : Fin 1 => (𝟙 C)) ≫ h = h
      rw [← Category.assoc, hret, Category.id_comp]
    · intro u hu
      rw [← hu, ← Category.assoc, hsec, Category.id_comp]

/-- **The trivial witness — kept deliberately, as the acceptance test for this file.**

`SymPowData C n` is inhabited for *every* `n` by taking `proj := 𝟙`, which makes the
universal property vacuous. This declaration exists so that the limitation is a checked
fact in the tree rather than a remark someone might doubt or forget.

Its purpose is contrastive: a downstream theorem is only meaningful because it *also*
requires `hproj : ∀ σ, permAut C σ ≫ D.proj = D.proj`, which this datum **fails** whenever
`permAut C σ ≠ 𝟙` — for `n ≥ 2` that holds as soon as `C` has two distinct global points
(`permAut_swap_ne_id_of_points`), though **not** at a terminal `C`, where it genuinely
satisfies `hproj` (`permAut_eq_id_of_isTerminal`); both in
`Albanese/SymPowColimit.lean`. Do not use it for anything; if a future
lemma over `SymPowData` can be instantiated at `symPowDataTrivial`, that lemma is
vacuous and the bug is in the lemma.

(The general lesson, arrived at independently in the `ajc-pic0av` lane the same day for
`PicScheme.ClassDegree`: an interface reduces something only when it asserts a
*nontrivial* property, and the test is to try inhabiting the thing your theorems
quantify over with a trivial witness. Recording the probe next to the structure is what
stops the failure mode, because a named-but-vacuous input reads as progress.) -/
noncomputable def symPowDataTrivial (C : K) (n : ℕ) : SymPowData C n where
  carrier := ∏ᶜ (fun _ : Fin n => C)
  proj := 𝟙 _
  desc := fun {_} h _ => ⟨h, Category.id_comp h, fun _ hu => by simpa using hu⟩

omit [CartesianMonoidalCategory K] in
/-- **The other half of the witness: `symPowDataOne`'s projection is symmetric.**

Every downstream theorem quantifies over a `SymPowData` *paired with* this hypothesis,
and the pairing is what rules out the trivial `proj := 𝟙` datum once `C` has two distinct
global points (see `permAut_swap_ne_id_of_points`; not at a terminal `C`). Here it is
immediate: `Equiv.Perm (Fin 1)` is a subsingleton, so `σ 0 = 0` and `permAut_π` closes
it.

Without this lemma the claim "the interface is inhabited" would not be machine-backed
end to end, since the bare structure is inhabited trivially. -/
theorem symPowDataOne_proj_perm (C : K) (σ : Equiv.Perm (Fin 1)) :
    MonObj.permAut C σ ≫ (symPowDataOne C).proj = (symPowDataOne C).proj := by
  have h : σ 0 = 0 := Subsingleton.elim _ _
  change MonObj.permAut C σ ≫ Pi.π (fun _ : Fin 1 => C) 0 = Pi.π (fun _ : Fin 1 => C) 0
  rw [MonObj.permAut_π, h]

end CategoryTheory
