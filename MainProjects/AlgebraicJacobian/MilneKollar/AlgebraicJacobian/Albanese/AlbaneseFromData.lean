/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Albanese.SymPowInterface
import AlgebraicJacobian.Albanese.DenseOpenDescent
import AlgebraicJacobian.Albanese.AVCommutative
import AlgebraicJacobian.Albanese.AVSelfProduct

/-!
# The Albanese universal property, proved over the symmetric-power interface

`Albanese/AlbaneseUP.lean` pins Milne's Proposition III.6.1 in the shape the
challenge wants, but its six obligations are stated against `Pic0.SymmetricPower`,
a `sorry`-bodied definition. An equation between morphisms out of a junk term
carries no information, so those obligations cannot be discharged — and should not
be, since discharging them would prove nothing.

This file does the mathematics instead. It takes the symmetric power as the
**interface** `SymPowData` (`Albanese/SymPowInterface.lean`), which is inhabited
(`symPowDataOne`), and proves Milne's argument over it with no `sorry` and no
appeal to an unproved statement. What the challenge still owes is then exactly one
thing — `SymPowData C g` for `g ≥ 2`, the missing scheme quotient — rather than six
entangled gaps.

## The two directions of the connector, and why each is now real

Milne's proof turns the Albanese equation `φ = aj ≫ ψ` into the symmetric-power
equation `Sym^g φ = f^{(g)} ≫ ψ`. Both directions are proved here:

* **Forward** (`symAVMap_eq_of_albanese_eq`). Assume `φ = aj ≫ ψ` where the
  Abel–Jacobi map is realised, as Milne realises it, through the basepoint shift:
  `aj = basePointShift P₀ i₀ ≫ proj ≫ f`. Then `Sym^g φ` and `f ≫ ψ` agree after
  `proj`, because pushing `ψ` through the `g`-fold sum is
  `map_prod (IsMonHom.monoidHom ψ _)` — this is where `ψ` being a *homomorphism*
  is used, and it is exactly Milne's step 5. Uniqueness in the interface then
  gives the equation on the carrier.
* **Backward** (`albanese_eq_of_symAVMap_eq`). Restrict along
  `Q ↦ (Q, P₀, …, P₀)` and collapse: `MonObj.basePointShift_comp_powSum`
  (proved in `SymPowInterface.lean`) says the `g`-fold sum of a *pointed* `φ` over
  that tuple is `φ` itself. No quotient property is needed for this direction at
  all — only the interface's defining equation.

## Main results

* `albaneseFactorisation_iff` — the connecting biconditional
  `(φ = aj ≫ ψ) ↔ (Sym^g φ = f ≫ ψ)`, over the interface. This is the honest form
  of `Pic0.albanese_eq_iff_symmetricPower_eq`.
* `exists_unique_albanese_factorisation` — **the Albanese universal property**:
  given the interface, the birational descent datum, and pointed rigidity, there is
  a unique `ψ` with `φ = aj ≫ ψ`. Milne Proposition III.6.1.
* `exists_unique_descent_of_section` (§2) — the descent datum supplied from its
  geometric source: a morphism on a dense open of the Jacobian. This is where
  `extend_to_av` (Milne I.3.2, proved and unconditional) does its work, and it is
  the form the eventual `Sym^g C` construction would feed.
* `exists_unique_descent_of_birational` (§2) — **Milne's step 2 in full.** The descent
  datum `hdesc` above, produced from exactly what Milne III.5.1(a) gives: a section of
  `f^{(g)}` over a dense open `V`, a matching retraction, and density of `V` and of
  `f⁻¹V`. Its conclusion `∃! ψ, h = f ≫ ψ` is an equation on *all* of `Sym^g C`, not
  merely on `V`, which is what the connector consumes.
* `exists_unique_descent_over` (§2) — the same datum transported from underlying
  scheme morphisms into `Over (Spec k̄)`, which is where the connector lives. The
  structure-map compatibility is **not** an extra hypothesis: it follows from
  dominance of `f` (`comp_hom_of_descent_eq`).
* `hom_ext_of_dense_open` — the agreement principle used for uniqueness.

## What remains, precisely

Only `SymPowData C g` for the actual curve and `g = genus C`, together with Milne
III.5.1(a) birationality in the concrete form `exists_unique_descent_of_birational`
consumes (section + retraction + two density facts). Everything Milne derives *from*
those is proved below — including, note, the step that used to be described as blocked
on "a way to invert a birational morphism": no birational-inverse API is needed, only
the section and retraction that birationality supplies directly.

## References

Milne, *Abelian Varieties*, §III.6 Proposition 6.1, p. 104; §III.5 Theorem 5.1(a),
p. 101; §I.3 Theorem 3.2. Blueprint `thm:albanese_universal_property` in
`blueprint/src/chapters/Albanese_AlbaneseUP.tex`.
-/

set_option autoImplicit false

universe v u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace CategoryTheory

/-! ## §1. The connector, in a general cartesian monoidal category

Both directions of Milne's biconditional are statements about monoid objects and
finite products; no geometry enters. We therefore prove them once, abstractly, and
instantiate at schemes in §2. -/

section Connector

variable {K : Type u} [Category.{v} K] [CartesianMonoidalCategory K]
  [HasFiniteProducts K] [BraidedCategory K]

variable {C J A : K} {g : ℕ}

/-! ### The hypotheses on `f^{(g)}`, and why they are the right two

Milne's cycle map is *defined* as the symmetrisation of the Abel–Jacobi map:
`f^{(g)} ∘ π = aj(P₁) + ⋯ + aj(P_g)`. That single equation (`hf` below) is the only
property of `f^{(g)}` the argument uses, and when `f = D.symAVMap aj` it holds by
`proj_comp_symAVMap`. The second hypothesis is Milne's basepoint condition
`aj(P₀) = η_J`, part of `lem:abel_jacobi_morphism`.

Together they *imply* Milne's identification of `aj` with `Q ↦ Q + (g−1) P₀`
followed by `f^{(g)}` — see `basePointShift_proj_comp`, which is
`basePointShift_comp_powSum` applied to `aj` itself. So that identification is
derived here, not assumed. -/

/-- **Milne's identification of the Abel–Jacobi map, derived.** If `f^{(g)}` is the
symmetrisation of a *pointed* `aj`, then `Q ↦ Q + (g−1) P₀` followed by `f^{(g)}`
is `aj`.

This is `basePointShift_comp_powSum` applied to `aj`: the `g`-fold sum of `aj` over
`(Q, P₀, …, P₀)` collapses to `aj(Q)` because `aj(P₀) = η_J`. -/
theorem basePointShift_proj_comp [MonObj J] [IsCommMonObj J]
    (D : SymPowData C g) (f : D.carrier ⟶ J) (P0 : 𝟙_ K ⟶ C) (i₀ : Fin g)
    (aj : C ⟶ J) (hf : D.proj ≫ f = powSum g aj) (haj0 : P0 ≫ aj = η[J]) :
    basePointShift P0 i₀ ≫ D.proj ≫ f = aj := by
  rw [hf]
  exact basePointShift_comp_powSum P0 i₀ aj haj0

/-- **Forward direction.** If `φ` factors through the Abel–Jacobi map, then
`Sym^g φ` factors through `f^{(g)}` with the same `ψ`.

The proof compares both sides after `proj`. On the left the interface's defining
equation gives the `g`-fold sum of `φ`; on the right `hf` gives the `g`-fold sum of
`aj`, then postcomposed with `ψ`. These agree because `ψ`, being a **homomorphism**
of monoid objects, commutes with a finite product in the hom-monoid
(`map_prod (IsMonHom.monoidHom ψ _)`) — this is where Milne's step 5 uses that `ψ`
is a homomorphism and not merely a morphism. Uniqueness through `proj` then upgrades
the agreement to the carrier. -/
theorem symAVMap_eq_of_albanese_eq
    [MonObj A] [IsCommMonObj A] [MonObj J] [IsCommMonObj J]
    (D : SymPowData C g) (f : D.carrier ⟶ J)
    (hproj : ∀ σ : Equiv.Perm (Fin g), MonObj.permAut C σ ≫ D.proj = D.proj)
    (aj : C ⟶ J) (hf : D.proj ≫ f = powSum g aj)
    (φ : C ⟶ A) (ψ : J ⟶ A) [IsMonHom ψ] (hφ : φ = aj ≫ ψ) :
    D.symAVMap φ = f ≫ ψ := by
  classical
  refine (D.hom_ext_of_proj hproj ?_).symm
  rw [D.proj_comp_symAVMap, ← Category.assoc, hf]
  -- `ψ` is a monoid-object homomorphism, so it commutes with the `g`-fold sum.
  rw [show (powSum g aj ≫ ψ) = ∏ i, ((Pi.π (fun _ : Fin g => C) i ≫ aj) ≫ ψ) from
    map_prod (IsMonHom.monoidHom ψ _) _ Finset.univ]
  rw [powSum]
  exact Finset.prod_congr rfl fun i _ => by rw [Category.assoc, ← hφ]

/-- **Backward direction.** If `Sym^g φ` factors through `f^{(g)}`, then `φ` factors
through the Abel–Jacobi map — provided `φ` is *pointed* (`P₀ ≫ φ = η[A]`).

This direction needs neither the quotient property nor that `ψ` is a homomorphism:
restrict the given equation along the basepoint shift `Q ↦ (Q, P₀, …, P₀)` and the
left side collapses to `φ` by `basePointShift_comp_powSum`, while the right side
becomes `aj ≫ ψ` by `basePointShift_proj_comp`. That is the whole force of Milne's
"restrict along `Q ↦ Q + (g−1) P₀` and use `φ(P₀) = η_A`". -/
theorem albanese_eq_of_symAVMap_eq
    [MonObj A] [IsCommMonObj A] [MonObj J] [IsCommMonObj J]
    (D : SymPowData C g) (f : D.carrier ⟶ J) (P0 : 𝟙_ K ⟶ C) (i₀ : Fin g)
    (aj : C ⟶ J) (hf : D.proj ≫ f = powSum g aj) (haj0 : P0 ≫ aj = η[J])
    (φ : C ⟶ A) (hφ : P0 ≫ φ = η[A]) (ψ : J ⟶ A)
    (h : D.symAVMap φ = f ≫ ψ) :
    φ = aj ≫ ψ := by
  have key : basePointShift P0 i₀ ≫ D.proj ≫ D.symAVMap φ
      = basePointShift P0 i₀ ≫ D.proj ≫ (f ≫ ψ) := by rw [h]
  rw [D.proj_comp_symAVMap, basePointShift_comp_powSum P0 i₀ φ hφ] at key
  rw [key, ← Category.assoc D.proj f ψ, ← Category.assoc,
    basePointShift_proj_comp D f P0 i₀ aj hf haj0]

/-- **The connecting biconditional (Milne's identification).** Over the symmetric-power
interface, the Albanese-form factorisation and the symmetric-power-form factorisation
of a pointed `φ` through a *homomorphism* `ψ` are equivalent.

This is the honest content of `Pic0.albanese_eq_iff_symmetricPower_eq`: same
mathematics, but stated about a symmetric power that is named rather than `sorry`ed,
so the equation says what it is meant to say. -/
theorem albaneseFactorisation_iff
    [MonObj A] [IsCommMonObj A] [MonObj J] [IsCommMonObj J]
    (D : SymPowData C g) (f : D.carrier ⟶ J) (P0 : 𝟙_ K ⟶ C) (i₀ : Fin g)
    (hproj : ∀ σ : Equiv.Perm (Fin g), MonObj.permAut C σ ≫ D.proj = D.proj)
    (aj : C ⟶ J) (hf : D.proj ≫ f = powSum g aj) (haj0 : P0 ≫ aj = η[J])
    (φ : C ⟶ A) (hφ : P0 ≫ φ = η[A]) (ψ : J ⟶ A) [IsMonHom ψ] :
    (φ = aj ≫ ψ) ↔ (D.symAVMap φ = f ≫ ψ) :=
  ⟨fun h => symAVMap_eq_of_albanese_eq D f hproj aj hf φ ψ h,
   fun h => albanese_eq_of_symAVMap_eq D f P0 i₀ aj hf haj0 φ hφ ψ h⟩

/-- **The Albanese universal property over the interface — Milne Proposition III.6.1.**

Given
* the symmetric-power interface `D` with symmetric projection `proj`,
* the cycle map `f = f^{(g)} : Sym^g C ⟶ J` presented as the symmetrisation of a
  pointed Abel–Jacobi map `aj` (`hf`, `haj0`),
* **pointed rigidity** (`hom`): every *pointed* morphism `J ⟶ A` is a homomorphism —
  Milne Corollary I.1.2, which for schemes is
  `AlgebraicGeometry.av_regularMap_isHom_of_zero` (proved, `RigidityLemma.lean`),
* the **descent datum** (`hdesc`): a unique `ψ` with `Sym^g φ = f ≫ ψ`,

there is a unique `ψ` with `φ = aj ≫ ψ`.

The proof is Milne's, transported across `albaneseFactorisation_iff`. Note that
`hom` is applied only after checking that the candidate `ψ` really is pointed, which
is itself derived: `η[J] = aj(P₀)` by `haj0`, so `η[J] ≫ ψ = φ(P₀) = η[A]`. Nothing
here rests on a `sorry`-bodied object; the descent datum is Milne's step 2 and is
supplied geometrically by `exists_unique_descent_of_section` in §2. -/
theorem exists_unique_albanese_factorisation
    [MonObj A] [IsCommMonObj A] [MonObj J] [IsCommMonObj J]
    (D : SymPowData C g) (f : D.carrier ⟶ J) (P0 : 𝟙_ K ⟶ C) (i₀ : Fin g)
    (hproj : ∀ σ : Equiv.Perm (Fin g), MonObj.permAut C σ ≫ D.proj = D.proj)
    (aj : C ⟶ J) (hf : D.proj ≫ f = powSum g aj) (haj0 : P0 ≫ aj = η[J])
    (φ : C ⟶ A) (hφ : P0 ≫ φ = η[A])
    (hom : ∀ ψ : J ⟶ A, η[J] ≫ ψ = η[A] → IsMonHom ψ)
    (hdesc : ∃! ψ : J ⟶ A, D.symAVMap φ = f ≫ ψ) :
    ∃! ψ : J ⟶ A, φ = aj ≫ ψ := by
  -- A `ψ` satisfying either factorisation is automatically pointed: `η[J] = aj(P₀)`.
  have hpt : ∀ ψ : J ⟶ A, φ = aj ≫ ψ → η[J] ≫ ψ = η[A] := by
    intro ψ hψ
    rw [← haj0, Category.assoc, ← hψ, hφ]
  obtain ⟨ψ, hψ, huniq⟩ := hdesc
  -- The witness is pointed *before* we may call rigidity, so establish that first
  -- from the symmetric-power side, via the backward direction.
  have hψalb : φ = aj ≫ ψ :=
    albanese_eq_of_symAVMap_eq D f P0 i₀ aj hf haj0 φ hφ ψ hψ
  refine ⟨ψ, hψalb, ?_⟩
  intro ψ' hψ'
  haveI := hom ψ' (hpt ψ' hψ')
  exact huniq ψ'
    ((albaneseFactorisation_iff D f P0 i₀ hproj aj hf haj0 φ hφ ψ').mp hψ')

end Connector

end CategoryTheory

/-! ## §2. Supplying the descent datum geometrically

At schemes over an algebraically closed field the descent datum of §1 is not an
assumption: it follows from a section of `f^{(g)}` over a dense open of the Jacobian,
by the rational-map extension `extend_to_av` (Milne I.3.2, proved and unconditional)
packaged as `exists_unique_hom_restrict_eq_of_dense_open`. -/

namespace AlgebraicGeometry

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

variable {kbar : Type u} [Field kbar] [IsAlgClosed kbar]

/-- **Milne's descent step, from birationality data.**

Let `J` be an abelian variety over `k̄`, let `V ⊆ J` be a **dense open**, and let
`s : V ⟶ Sym^g C` be a section of `f^{(g)}` over `V` (i.e. `s ≫ f = V.ι`, which is
what birationality of `f^{(g)}` provides — Milne III.5.1(a)). Then for any
`h : Sym^g C ⟶ A` there is a unique `ψ : J ⟶ A` with `V.ι ≫ ψ = s ≫ h`.

Existence and uniqueness are `exists_unique_hom_restrict_eq_of_dense_open`, i.e.
Milne Theorem I.3.2; the section is the only new input. This is the *only* step of
the Albanese proof that uses the rational-map extension, and its input is now
completely explicit. -/
theorem exists_unique_descent_of_section
    {J : Over (Spec (.of kbar))}
    [Smooth J.hom] [GeometricallyIrreducible J.hom] [IsSeparated J.hom]
    [LocallyOfFiniteType J.hom] [IsIntegral J.left] [IsReduced J.left]
    {A : Over (Spec (.of kbar))}
    [GrpObj A] [IsProper A.hom] [Smooth A.hom] [GeometricallyIrreducible A.hom]
    (V : J.left.Opens) (hV : Dense (V : Set J.left)) (k : (V : Scheme) ⟶ A.left)
    (hover : (Scheme.PartialMap.mk V hV k).toRationalMap.compHom A.hom
      = J.hom.toRationalMap) :
    ∃! ψ : J.left ⟶ A.left, V.ι ≫ ψ = k :=
  Scheme.RationalMap.exists_unique_hom_restrict_eq_of_dense_open V hV k hover

/-- **A dense open inclusion is dominant.** Used to transport an equation proved on a
dense open to the whole (reduced) scheme. -/
theorem isDominant_opens_ι {X : Scheme.{u}} (V : X.Opens) (hV : Dense (V : Set X)) :
    IsDominant V.ι := by
  rw [isDominant_iff]
  simpa [DenseRange, Scheme.Opens.range_ι] using hV

/-- **Milne's step 2 in full, from birationality data.**

This is the descent datum `hdesc` of `exists_unique_albanese_factorisation`, produced
from exactly what Milne III.5.1(a) provides. Suppose `f : S ⟶ J` (morally
`f^{(g)} : Sym^g C ⟶ Pic⁰`) is an **isomorphism over a dense open** `V ⊆ J`, presented
concretely as

* `s : V ⟶ S` with `s ≫ f = V.ι` — a section of `f` over `V`;
* `hsr` — and `s` is also a retraction of the restriction `f|_{f⁻¹V} : f⁻¹V ⟶ V`;
* `hVpre` — the preimage `f⁻¹V` is dense in `S`.

Then for any `h : S ⟶ A` into an abelian variety there is a **unique** `ψ : J ⟶ A`
with `h = f ≫ ψ`.

Note the shape of the conclusion: the equation is on **all** of `S`, not merely on
`V`. That is the difference between this and
`exists_unique_hom_restrict_eq_of_dense_open`, and it is where `hsr` and `hVpre` earn
their place — the extension theorem gives the equation on `V`, and agreement is then
transported to all of `S` along the dense open `f⁻¹V` (`ext_of_isDominant`, using that
`S` is reduced and `A` separated).

So the Albanese descent needs no birational-inverse API. The full call-site bill is
**five** items, not four: the section `s`, the retraction `hsr`, the two density facts
`hV` and `hVpre`, and `hover` — the compatibility of the partial map with the structure
morphisms over `k̄`, which is what `exists_unique_hom_restrict_eq_of_dense_open`
(`Albanese/DenseOpenDescent.lean`) consumes. `hover` is a genuine hypothesis; it is
listed here because an earlier draft of this docstring omitted it. -/
theorem exists_unique_descent_of_birational
    {S J : Over (Spec (.of kbar))} [IsReduced S.left]
    [Smooth J.hom] [GeometricallyIrreducible J.hom] [IsSeparated J.hom]
    [LocallyOfFiniteType J.hom] [IsIntegral J.left] [IsReduced J.left]
    {A : Over (Spec (.of kbar))}
    [GrpObj A] [IsProper A.hom] [Smooth A.hom] [GeometricallyIrreducible A.hom]
    (f : S.left ⟶ J.left) (h : S.left ⟶ A.left)
    (V : J.left.Opens) (hV : Dense (V : Set J.left))
    (hVpre : Dense ((f ⁻¹ᵁ V : S.left.Opens) : Set S.left))
    (s : (V : Scheme) ⟶ S.left) (hs : s ≫ f = V.ι)
    (hsr : f.resLE V (f ⁻¹ᵁ V) le_rfl ≫ s = (f ⁻¹ᵁ V).ι)
    (hover : (Scheme.PartialMap.mk V hV (s ≫ h)).toRationalMap.compHom A.hom
      = J.hom.toRationalMap) :
    ∃! ψ : J.left ⟶ A.left, h = f ≫ ψ := by
  haveI : A.left.IsSeparated := Scheme.RationalMap.isSeparated_left_of_isProper A
  haveI hdom : IsDominant (f ⁻¹ᵁ V).ι := by
    rw [isDominant_iff]
    simpa [DenseRange, Scheme.Opens.range_ι] using hVpre
  obtain ⟨ψ, hψ, huniq⟩ :=
    Scheme.RationalMap.exists_unique_hom_restrict_eq_of_dense_open V hV (s ≫ h) hover
  refine ⟨ψ, ?_, ?_⟩
  · -- Both sides agree on the dense open `f⁻¹(V)`; transport to all of `S`.
    refine ext_of_isDominant (f ⁻¹ᵁ V).ι ?_
    calc (f ⁻¹ᵁ V).ι ≫ h
        = (f.resLE V (f ⁻¹ᵁ V) le_rfl ≫ s) ≫ h := by rw [hsr]
      _ = f.resLE V (f ⁻¹ᵁ V) le_rfl ≫ (s ≫ h) := by simp
      _ = f.resLE V (f ⁻¹ᵁ V) le_rfl ≫ (V.ι ≫ ψ) := by rw [hψ]
      _ = (f ⁻¹ᵁ V).ι ≫ f ≫ ψ := by
            rw [← Category.assoc,
              show f.resLE V (f ⁻¹ᵁ V) le_rfl ≫ V.ι = (f ⁻¹ᵁ V).ι ≫ f from by
                simp [Scheme.Hom.resLE], Category.assoc]
  · intro ψ' hψ'
    refine huniq ψ' ?_
    change V.ι ≫ ψ' = s ≫ h
    rw [← hs, Category.assoc, ← hψ']

/-! ### Crossing from scheme morphisms to `Over (Spec k̄)` morphisms

`exists_unique_descent_of_birational` concludes about `J.left ⟶ A.left`, whereas the
connector of §1 lives in `Over (Spec k̄)`. The two lemmas below cross that gap, and the
crossing is free rather than an extra hypothesis: compatibility with the structure
morphisms is *automatic* once `f` is dominant. -/

omit [IsAlgClosed kbar] in
/-- **Compatibility over `k̄` is automatic.** If `f : S ⟶ J` has dominant underlying
morphism and `ψ` satisfies `h.left = f.left ≫ ψ`, then `ψ` is a morphism over `k̄`:
`ψ ≫ A.hom = J.hom`.

Both sides agree after the dominant `f.left` (each reduces to the structure morphism of
`S`, by `h.w` and `f.w`), and `J.left` is reduced, so `ext_of_isDominant` concludes.
This is why the descent produces an honest `Over` morphism without assuming it. -/
theorem comp_hom_of_descent_eq
    {S J A : Over (Spec (.of kbar))} [IsReduced J.left]
    (f : S ⟶ J) (h : S ⟶ A) (ψ : J.left ⟶ A.left)
    (hfd : IsDominant f.left) (hψ : h.left = f.left ≫ ψ) :
    ψ ≫ A.hom = J.hom := by
  refine ext_of_isDominant f.left ?_
  rw [← Category.assoc, ← hψ]
  exact h.w.trans f.w.symm

omit [IsAlgClosed kbar] in
/-- **Transport the descent datum into `Over (Spec k̄)`.** A unique factorisation of
underlying scheme morphisms upgrades to a unique factorisation of `k̄`-morphisms, using
`comp_hom_of_descent_eq` for the structure-map compatibility.

This delivers `hdesc` in exactly the shape `exists_unique_albanese_factorisation`
consumes. -/
theorem exists_unique_descent_over
    {S J A : Over (Spec (.of kbar))} [IsReduced J.left]
    (f : S ⟶ J) (h : S ⟶ A) (hfd : IsDominant f.left)
    (hyp : ∃! ψ : J.left ⟶ A.left, h.left = f.left ≫ ψ) :
    ∃! ψ : J ⟶ A, h = f ≫ ψ := by
  obtain ⟨ψ, hψ, huniq⟩ := hyp
  refine ⟨Over.homMk ψ (comp_hom_of_descent_eq f h ψ hfd hψ),
    Over.OverMorphism.ext (by simpa using hψ), ?_⟩
  intro ψ' hψ'
  refine Over.OverMorphism.ext ?_
  exact huniq ψ'.left (by simpa using congrArg Over.Hom.left (a₁ := h) hψ')

omit [IsAlgClosed kbar] in
/-- **Uniqueness of the Albanese descent, geometrically.** Two morphisms from the
Jacobian to an abelian variety that agree on a dense open are equal — the
reduced-and-separated agreement principle, in the form the descent uses. -/
theorem hom_ext_of_dense_open
    {J : Over (Spec (.of kbar))} [IsReduced J.left]
    {A : Over (Spec (.of kbar))} [IsProper A.hom]
    (V : J.left.Opens) (hV : Dense (V : Set J.left))
    {ψ₁ ψ₂ : J.left ⟶ A.left} (h : V.ι ≫ ψ₁ = V.ι ≫ ψ₂) : ψ₁ = ψ₂ := by
  haveI : A.left.IsSeparated := Scheme.RationalMap.isSeparated_left_of_isProper A
  haveI := isDominant_opens_ι V hV
  exact ext_of_isDominant V.ι h

/-! ## §3. End to end: `SymPowData` + birationality ⟹ the Albanese universal property

The capstone. Everything above is assembled into one statement whose hypotheses are
**only** the two things this leg genuinely owes:

1. `D : SymPowData C g` — the symmetric power with its universal property;
2. Milne III.5.1(a) birationality of `f^{(g)}`, in the concrete form of a section `s`
   over a dense open `V`, a matching retraction, dominance, and two density facts.

No `sorry`-bodied object appears, no rational-map reasoning is left at the call site,
and the result is axiom-clean.

**Stated precisely, so "finished" is not read too generously.** What is proved is the
*implication*: given (1) and (2), Milne III.6.1 holds. Every step of his argument is
machine-checked, and no step of it is what remains. But the antecedent is currently
witnessed only for `g = 1` (`symPowDataOne` with `symPowDataOne_proj_perm`), which is
the case where the group-law step degenerates — see the warning in
`Albanese/SymPowInterface.lean`. So this is a complete argument awaiting a
construction, not a theorem about the actual `Sym^g C`. -/

/-- **Milne Proposition III.6.1, end to end.**

From the symmetric-power interface and Milne III.5.1(a)'s birationality data alone, a
pointed `φ : C ⟶ A` into an abelian variety factors uniquely through the pointed
`aj : C ⟶ J` whose symmetrisation is `f`:

`∃! ψ : J ⟶ A, φ = aj ≫ ψ`.

**Axiom-clean** (`[propext, Classical.choice, Quot.sound]`). The chain is
`exists_unique_descent_of_birational` → `exists_unique_descent_over` →
`exists_unique_albanese_factorisation`, with commutativity and pointed rigidity
supplied by `Albanese/AVSelfProduct.lean`.

Note that no curve hypothesis appears: `g` is just the number of factors. -/
theorem exists_unique_albanese_factorisation_of_birational
    {C : Over (Spec (.of kbar))} {g : ℕ}
    (D : SymPowData C g)
    (hproj : ∀ σ : Equiv.Perm (Fin g), permAut C σ ≫ D.proj = D.proj)
    (P0 : 𝟙_ (Over (Spec (.of kbar))) ⟶ C) (i₀ : Fin g)
    {J A : Over (Spec (.of kbar))}
    [GrpObj J] [IsProper J.hom] [Smooth J.hom] [GeometricallyIrreducible J.hom]
    [IsIntegral J.left] [IsReduced J.left]
    [GrpObj A] [IsProper A.hom] [Smooth A.hom] [GeometricallyIrreducible A.hom]
    [IsReduced (D.carrier).left]
    (φ : C ⟶ A) (hφ : P0 ≫ φ = η[A])
    (aj : C ⟶ J) (f : D.carrier ⟶ J)
    (hf : letI : IsCommMonObj J := isCommMonObj_of_isProper_smooth_of_package J
      D.proj ≫ f = powSum g aj)
    (haj0 : P0 ≫ aj = η[J])
    (hfd : IsDominant f.left)
    (V : J.left.Opens) (hV : Dense (V : Set J.left))
    (hVpre : Dense ((f.left ⁻¹ᵁ V : (D.carrier).left.Opens) : Set (D.carrier).left))
    (s : (V : Scheme) ⟶ (D.carrier).left) (hs : s ≫ f.left = V.ι)
    (hsr : f.left.resLE V (f.left ⁻¹ᵁ V) le_rfl ≫ s = (f.left ⁻¹ᵁ V).ι)
    (hover : letI : IsCommMonObj A := isCommMonObj_of_isProper_smooth_of_package A
      (Scheme.PartialMap.mk V hV (s ≫ (D.symAVMap φ).left)).toRationalMap.compHom A.hom
        = J.hom.toRationalMap) :
    ∃! ψ : J ⟶ A, φ = aj ≫ ψ := by
  letI : IsCommMonObj J := isCommMonObj_of_isProper_smooth_of_package J
  letI : IsCommMonObj A := isCommMonObj_of_isProper_smooth_of_package A
  refine exists_unique_albanese_factorisation D f P0 i₀ hproj aj hf haj0 φ hφ
    (fun ψ hψ => isMonHom_of_pointed ψ hψ) ?_
  exact exists_unique_descent_over f (D.symAVMap φ) hfd
    (exists_unique_descent_of_birational f.left (D.symAVMap φ).left V hV hVpre s hs hsr hover)

end AlgebraicGeometry
