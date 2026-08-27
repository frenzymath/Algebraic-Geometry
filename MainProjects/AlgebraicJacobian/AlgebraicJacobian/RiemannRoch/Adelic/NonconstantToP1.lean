/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.RiemannRoch.Adelic.FiniteMapToP1
import AlgebraicJacobian.Picard.ProjectiveSpace
import AlgebraicJacobian.Picard.SerreTwist
import AlgebraicJacobian.Albanese.CodimOneExtension
import AlgebraicJacobian.Albanese.StandardSmoothDimension

/-!
# Reducing the nonconstant-map gate to the integral `Proj` model (node `N9a`)

This file peels the *base-change / over-`k` layer* off the last open gate of the
adelic finite-map chain, `Adelic.ExistsNonconstantMapToP1` (`FiniteMapToP1.lean`,
node `N9a`).  That gate asks for a nonconstant `k`-morphism into the concrete
projective line
`ℙ¹_k = ℙ(ULift (Fin 2); Spec k)`, which by construction
(`Picard/ProjectiveSpace.lean`) is the base change of the **integral model**
`Proj ℤ[X₀, X₁] = Proj (homogeneousSubmodule (ULift (Fin 2)) (ULift ℤ))` along the
terminal map `Spec k ⟶ ⊤_ Scheme`:
```
ℙ¹_k  =  Spec k  ×_{⊤}  Proj ℤ[X₀, X₁].
```

Because `ℙ¹_k` is a fibre product over the *terminal* object, the pullback
compatibility square is discharged automatically (any two morphisms into `⊤_
Scheme` agree), so the universal property of the pullback turns a bare scheme
morphism `C ⟶ Proj ℤ[X₀, X₁]` — with **no** over-`k` or terminal bookkeeping —
together with the ambient structure map `C ⟶ Spec k` into a genuine `k`-morphism
`C ⟶ ℙ¹_k`.  Nonconstancy transfers verbatim: the projection
`ℙ¹_k ⟶ Proj ℤ[X₀, X₁]` (`ProjectiveSpace.toProjInt`) sends the built morphism
back to the given one, so two distinct point-images upstairs force two distinct
point-images downstairs.

## Main results

* `Adelic.ExistsNonconstantMapToProjInt C` — the **cleaner residual gate**: a
  nonconstant scheme morphism `C.left ⟶ Proj ℤ[X₀, X₁]` (two distinct
  point-images), phrased entirely inside the concrete integral `Proj` model where
  `P1ChartData.lean` already computes the standard chart coordinates
  `x = X₁/X₀`, `y = X₀/X₁`.
* `Adelic.existsNonconstantMapToP1_of_nonconstantMapToProjInt` — the **bridge
  theorem** (reusable constructor): any nonconstant `C.left ⟶ Proj ℤ[X₀, X₁]`
  yields `ExistsNonconstantMapToP1 C`, via `pullback.lift` + terminal
  uniqueness.
* `Adelic.existsNonconstantMapToP1_of_existsNonconstantMapToProjInt` — the
  derived instance discharging `ExistsNonconstantMapToP1 C` from the cleaner gate,
  so the whole finite-map chain now bottoms out at `ExistsNonconstantMapToProjInt`.
* `Adelic.existsNonconstantMapToProjInt_of_ajc` — **the gate is now DISCHARGED**:
  for the AJC curve (`SmoothOfRelativeDimension 1` + `IsProper` +
  `GeometricallyIntegral` over an arbitrary field `k`) the instance
  `ExistsNonconstantMapToProjInt C` is *proved*, closing the last gate of the
  adelic finite-map chain (see the section documentation below for the two-chart
  construction: pole datum → regularity loci → faithfully-flat valuative
  dichotomy over the algebraic closure → gluing → nonconstancy).  Together with
  the previously-proved chain this makes `HasFiniteMapToP1 C` **unconditional**
  for every AJC curve.

Blueprint node: `thm:adelic_exists_finiteMorphismToP1` (gate `N9a`, now closed).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MvPolynomial

namespace AlgebraicGeometry.Adelic

variable {k : Type u} [Field k]

/-- **The residual nonconstant-map gate at the integral `Proj` model (node `N9a`).**
A single-field `Prop` class asserting the existence of a nonconstant scheme
morphism from the curve `C` to the integral model of the projective line
`Proj ℤ[X₀, X₁] = Proj (homogeneousSubmodule (ULift (Fin 2)) (ULift ℤ))`
(nonconstant = two distinct point-images).

This is the base-change-free heart of `ExistsNonconstantMapToP1`: the over-`k`
structure and the fibre-product-over-terminal bookkeeping have been discharged in
`existsNonconstantMapToP1_of_nonconstantMapToProjInt`, so what remains is the
genuine curve theory (a nonconstant rational function whose chart morphisms glue
by the valuative dichotomy — see the module header).  For the AJC curve the class
is **discharged** by the instance `existsNonconstantMapToProjInt_of_ajc` at the
bottom of this file. -/
class ExistsNonconstantMapToProjInt (C : Over (Spec (CommRingCat.of k))) : Prop where
  /-- There exists a nonconstant scheme morphism `C ⟶ Proj ℤ[X₀, X₁]`. -/
  exists_nonconstant_map :
    ∃ f : C.left ⟶ Proj (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)),
      ∃ x₁ x₂ : C.left, f x₁ ≠ f x₂

/-- **The base-change bridge (node `N9a` discharge, reusable constructor).**
Any nonconstant scheme morphism `f : C.left ⟶ Proj ℤ[X₀, X₁]` into the integral
model of the projective line yields the finite-map gate input
`ExistsNonconstantMapToP1 C`.

`ℙ¹_k = Spec k ×_{⊤} Proj ℤ[X₀, X₁]` is a fibre product over the terminal object,
so the compatibility square for `pullback.lift` collapses to the uniqueness of
morphisms into `⊤_ Scheme`; the lift of the ambient structure map `C ↘ Spec k`
and of `f` is a `k`-morphism `C ⟶ ℙ¹_k` whose composite with the projection
`ProjectiveSpace.toProjInt` back to `Proj ℤ[X₀, X₁]` is `f` again, so the two
distinct point-images of `f` are preserved. -/
theorem existsNonconstantMapToP1_of_nonconstantMapToProjInt
    (C : Over (Spec (CommRingCat.of k)))
    (f : C.left ⟶ Proj (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)))
    (hf : ∃ x₁ x₂ : C.left, f x₁ ≠ f x₂) :
    ExistsNonconstantMapToP1 C := by
  obtain ⟨x₁, x₂, hx⟩ := hf
  -- The compatibility square lives over the terminal object, hence is automatic.
  have hcomm : C.hom ≫ terminal.from (Spec (CommRingCat.of k))
      = f ≫ terminal.from (Proj (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))) :=
    Subsingleton.elim _ _
  -- The lift into `ℙ¹_k = Spec k ×_{⊤} Proj ℤ[X₀, X₁]`.
  let g : C.left ⟶ ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) :=
    pullback.lift C.hom f hcomm
  have hfst : g ≫ (ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) ↘
      Spec (CommRingCat.of k)) = C.hom := by
    rw [ProjectiveSpace.over_eq_fst]; exact pullback.lift_fst _ _ _
  have hsnd : g ≫ ProjectiveSpace.toProjInt (ULift.{u} (Fin 2))
      (Spec (CommRingCat.of k)) = f := by
    rw [ProjectiveSpace.toProjInt_eq_snd]; exact pullback.lift_snd _ _ _
  -- Package as a `k`-morphism and transfer nonconstancy through `toProjInt`.
  refine ⟨⟨Over.homMk g hfst, x₁, x₂, ?_⟩⟩
  simp only [Over.homMk_left]
  intro hg
  apply hx
  rw [← hsnd, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  exact congrArg _ hg

/-- **The finite-map gate through the cleaner `Proj`-model gate (node `N9a`).**
`ExistsNonconstantMapToP1 C` follows from the base-change-free gate
`ExistsNonconstantMapToProjInt C`, so the adelic finite-map chain now bottoms out
at the concrete integral `Proj` model. -/
instance (priority := 100) existsNonconstantMapToP1_of_existsNonconstantMapToProjInt
    (C : Over (Spec (CommRingCat.of k))) [ExistsNonconstantMapToProjInt C] :
    ExistsNonconstantMapToP1 C := by
  obtain ⟨f, hf⟩ := ExistsNonconstantMapToProjInt.exists_nonconstant_map (C := C)
  exact existsNonconstantMapToP1_of_nonconstantMapToProjInt C f hf

/-!
## Discharging the gate: the two-chart construction of a nonconstant map to `Proj ℤ[X₀,X₁]`

The remainder of this file **proves** `ExistsNonconstantMapToProjInt C` for the AJC curve
(`SmoothOfRelativeDimension 1` + `IsProper` + `GeometricallyIntegral` over any field `k`),
closing the last gate of the finite-map chain.  The route:

1. **A rational function with a pole** (`exists_pole`).  The curve has a point `x ≠ η`
   (the standard-smooth charts have Krull dimension `≥ 1` by the height lower bound of
   `Albanese/StandardSmoothDimension.lean`), whose stalk is a local domain with nonzero
   maximal ideal; for `0 ≠ π ∈ 𝔪ₓ` the rational function `t = 1/π ∈ K(C)` is regular
   nowhere-vanishing at the generic point and has a **pole at `x`** (it does *not* lie in
   the image of `𝒪_{C,x} → K(C)`, while `t⁻¹ = π` does).

2. **The regularity locus** (`regLocus`, `regSection`).  For `t ∈ K(C)` the locus
   `L(t) ⊆ C` of points at whose stalks `t` is regular is open, and by the sheaf axiom
   (`TopCat.Sheaf.existsUnique_gluing'`, gluing along `germToFunctionField`-injectivity on
   the integral `C`) it carries a canonical section `regSection t ∈ Γ(C, L(t))` mapping to
   `t` in `K(C)` at every point.

3. **The valuative dichotomy** (`regLocus_sup_regLocus_inv_eq_top`): `L(t) ∪ L(t⁻¹) = C`.
   At a closed point `w` the honest input is that `𝒪_{C,w}` becomes a DVR after the flat
   local base change to the algebraic closure `k̄`: the stalk of `C_{k̄} = C ×_k k̄` at a
   point over `w` is a DVR by `Scheme.localRing_dvr_of_codim_one`
   (`Albanese/CodimOneExtension.lean`, over the algebraically closed `k̄`), and the
   valuation dichotomy *descends* along the faithfully flat stalk map
   (`Module.FaithfullyFlat.of_flat_of_isLocalHom` + the divisibility descent
   `Ideal.comap_map_eq_self_of_faithfullyFlat`) — see
   `mem_range_algebraMap_or_inv_mem_range` below.  This is exactly how the smooth ⟹
   regular pipeline avoids its current perfect-field restriction.

4. **The two chart morphisms and gluing** (`chartMor₀`, `chartMor₁`,
   `nonconstantMapToProjInt`).  `t` (resp. `t⁻¹`) defines `L(t) ⟶ Spec ℤ[X₁/X₀] ⟶ Proj`
   classified by the evaluation `X₀ ↦ 1, X₁ ↦ t` (resp. `X₀ ↦ t⁻¹, X₁ ↦ 1`); on the
   overlap both factor through the chart `D₊(X₀X₁)` with *equal* classifying maps (the
   homogeneous-evaluation identity `p1Eval_swap` for the unit pair `t·t⁻¹ = 1`), so they
   glue over the cover `L(t) ∪ L(t⁻¹) = C` (`Scheme.Cover.glueMorphisms`).

5. **Nonconstancy**: the glued morphism sends `η` into `D₊(X₀)` and the pole `x` outside
   it (`chartMor₁_preimage_basicOpen`: the pullback of `D₊(X₀)` along the second chart is
   the non-vanishing locus of `t⁻¹`, and `t⁻¹(x) = π(x) = 0`).
-/

/-! ### Faithfully flat descent of divisibility, and the valuation-ring dichotomy -/

section FaithfullyFlatDescent

/-- **Divisibility descends along a faithfully flat algebra.**  If `φ(a) = b · φ(s)` in a
faithfully flat `A`-algebra `B`, then already `s ∣ a` in `A`: the contraction of the
extended ideal `(s)B` is `(s)` (`Ideal.comap_map_eq_self_of_faithfullyFlat`). -/
theorem exists_eq_mul_of_faithfullyFlat {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Module.FaithfullyFlat A B] {a s : A} {b : B}
    (h : algebraMap A B a = b * algebraMap A B s) : ∃ c : A, a = s * c := by
  have hmem : a ∈ ((Ideal.span {s} : Ideal A).map (algebraMap A B)).comap (algebraMap A B) := by
    rw [Ideal.mem_comap, Ideal.map_span, Set.image_singleton]
    exact Ideal.mem_span_singleton'.mpr ⟨b, h.symm⟩
  rw [Ideal.comap_map_eq_self_of_faithfullyFlat] at hmem
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  exact ⟨c, by rw [← hc, mul_comm]⟩

/-- **The valuation dichotomy descends along a faithfully flat extension of local
domains.**  Let `K = Frac A`, and let `B` be a faithfully flat `A`-algebra which is a
valuation ring with fraction field `L`.  Then every nonzero `t ∈ K` satisfies `t ∈ A` or
`t⁻¹ ∈ A` (as subrings of `K`): the dichotomy holds in the valuation ring `B`, and
divisibility descends by faithful flatness.  Applied with `B` the DVR stalk of the
base-changed curve `C_{k̄}`, this is the arbitrary-field replacement for the
"stalks of a smooth curve are DVRs" step. -/
theorem mem_range_algebraMap_or_inv_mem_range {A B K L : Type*}
    [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [ValuationRing B]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [IsFractionRing B L] [Algebra A B] [Module.FaithfullyFlat A B]
    (t : K) (ht : t ≠ 0) :
    t ∈ Set.range (algebraMap A K) ∨ t⁻¹ ∈ Set.range (algebraMap A K) := by
  have hABinj : Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B
  have hginj : Function.Injective ((algebraMap B L).comp (algebraMap A B)) :=
    (IsFractionRing.injective B L).comp hABinj
  set j : K →+* L := IsFractionRing.lift hginj with hjdef
  have hjalg : ∀ a : A, j (algebraMap A K a) = algebraMap B L (algebraMap A B a) := fun a => by
    rw [hjdef, IsFractionRing.lift_algebraMap, RingHom.comp_apply]
  have hjinj : Function.Injective j := j.injective
  obtain ⟨a, s, hs, hts⟩ := IsFractionRing.div_surjective (A := A) t
  have hsK : algebraMap A K s ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr (nonZeroDivisors.ne_zero hs)
  have haK : algebraMap A K a = t * algebraMap A K s := by
    rw [← hts, div_mul_cancel₀ _ hsK]
  have haK0 : algebraMap A K a ≠ 0 := haK ▸ mul_ne_zero ht hsK
  have hjt0 : j t ≠ 0 := (map_ne_zero_iff j hjinj).mpr ht
  rcases ValuationRing.isInteger_or_isInteger B (j t) with ⟨b, hb⟩ | ⟨b, hb⟩
  · left
    have hfb : algebraMap A B a = b * algebraMap A B s := by
      apply IsFractionRing.injective B L
      rw [map_mul, hb, ← hjalg, ← hjalg, haK, map_mul]
    obtain ⟨c, hc⟩ := exists_eq_mul_of_faithfullyFlat hfb
    refine ⟨c, ?_⟩
    have hK : algebraMap A K a = algebraMap A K s * algebraMap A K c := by
      rw [hc, map_mul]
    rw [← hts, hK, mul_div_cancel_left₀ _ hsK]
  · right
    have hfb : algebraMap A B s = b * algebraMap A B a := by
      apply IsFractionRing.injective B L
      have hjs : j (algebraMap A K a) = j t * j (algebraMap A K s) := by
        rw [haK, map_mul]
      rw [map_mul, hb, ← hjalg, ← hjalg, hjs, inv_mul_cancel_left₀ hjt0]
    obtain ⟨c, hc⟩ := exists_eq_mul_of_faithfullyFlat hfb
    refine ⟨c, ?_⟩
    have hK : algebraMap A K s = algebraMap A K a * algebraMap A K c := by
      rw [hc, map_mul]
    rw [← hts, inv_div, hK, mul_div_cancel_left₀ _ haK0]

end FaithfullyFlatDescent

/-! ### The chart ring-hom calculus for `Proj ℤ[X₀, X₁]`

For a commutative ring `B` and elements `b₀, b₁ ∈ B`, evaluation `X₀ ↦ b₀, X₁ ↦ b₁`
defines `p1Eval b₀ b₁ : ℤ[X₀,X₁] →+* B`; whenever the image of the localizing variable is
a unit it lifts to the degree-zero away rings `(ℤ[X₀,X₁]_f)₀` (`awayLift`), giving the
classifying ring maps of the two chart morphisms and of their common overlap chart
`D₊(X₀X₁)`.  All identities are proved through the normal form
`awayLift f ψ hu (a / fⁿ) · ψ(f)ⁿ = ψ(a)` (`awayLift_mul_eq`). -/

section ChartHoms

open HomogeneousLocalization

variable {B B' : Type*} [CommRing B] [CommRing B']

/-- Evaluation `X₀ ↦ b₀, X₁ ↦ b₁` on the integral model's coordinate ring. -/
private def p1Eval (b₀ b₁ : B) : (MvPolynomial (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) →+* B :=
  eval₂Hom ((Int.castRingHom B).comp (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toRingHom)
    (fun i : ULift.{u} (Fin 2) => ![b₀, b₁] i.down)

@[simp]
private lemma p1Eval_X0 (b₀ b₁ : B) : p1Eval b₀ b₁ (X ⟨0⟩) = b₀ := by
  simp [p1Eval]

@[simp]
private lemma p1Eval_X1 (b₀ b₁ : B) : p1Eval b₀ b₁ (X ⟨1⟩) = b₁ := by
  simp [p1Eval]

/-- Post-composition with a ring hom commutes with the evaluation. -/
private lemma comp_p1Eval (r : B →+* B') (b₀ b₁ : B) :
    r.comp (p1Eval b₀ b₁) = p1Eval (r b₀) (r b₁) := by
  apply MvPolynomial.ringHom_ext
  · intro z
    simp [p1Eval]
  · intro i
    rcases i with ⟨i⟩
    fin_cases i <;> simp [p1Eval]

/-- Two-variable monomial evaluation. -/
private lemma p1Eval_monomial (b₀ b₁ : B) (d : ULift.{u} (Fin 2) →₀ ℕ) (c : ULift.{u} ℤ) :
    p1Eval b₀ b₁ (monomial d c) = (c.down : B) * (b₀ ^ d ⟨0⟩ * b₁ ^ d ⟨1⟩) := by
  simp only [p1Eval, coe_eval₂Hom]
  rw [MvPolynomial.eval₂_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
  congr 1
  rw [← Equiv.prod_comp (Equiv.ulift.symm : Fin 2 ≃ ULift.{u} (Fin 2))
    (fun i => (![b₀, b₁] i.down) ^ d i), Fin.prod_univ_two]
  rfl

/-- On the support of a two-variable homogeneous polynomial of degree `m`, the exponents
sum to `m`. -/
private lemma support_exponent_sum {a : MvPolynomial (ULift.{u} (Fin 2)) (ULift.{u} ℤ)}
    {m : ℕ} (ha : a.IsHomogeneous m)
    {d : ULift.{u} (Fin 2) →₀ ℕ} (hd : d ∈ a.support) : d ⟨0⟩ + d ⟨1⟩ = m := by
  rw [mem_support_iff] at hd
  have hdeg : Finsupp.degree d = m := by
    by_contra hne
    exact hd (ha.coeff_eq_zero hne)
  rw [Finsupp.degree_eq_sum,
    ← Equiv.sum_comp (Equiv.ulift.symm : Fin 2 ≃ ULift.{u} (Fin 2)) (fun i => d i),
    Fin.sum_univ_two] at hdeg
  simpa using hdeg

/-- **The homogeneous swap identity.**  For a unit pair `b·b' = 1` and a homogeneous
polynomial `a` of degree `m`, evaluating at `(b', 1)` and at `(1, b)` differ by `b'^m`.
This is the coordinate-change identity underlying the agreement of the two chart maps on
the overlap `D₊(X₀X₁)`. -/
private lemma p1Eval_swap {b b' : B} (hbb' : b * b' = 1) {m : ℕ}
    {a : (MvPolynomial (ULift.{u} (Fin 2)) (ULift.{u} ℤ))} (ha : a.IsHomogeneous m) :
    p1Eval b' 1 a = b' ^ m * p1Eval 1 b a := by
  conv_lhs => rw [a.as_sum]
  conv_rhs => rw [a.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hsum := support_exponent_sum ha hd
  rw [p1Eval_monomial, p1Eval_monomial, one_pow, one_pow, mul_one, one_mul]
  rw [← mul_assoc, mul_comm (b' ^ m) ((coeff d a).down : B), mul_assoc]
  congr 1
  rw [← hsum, pow_add, mul_assoc, ← mul_pow, mul_comm b' b, hbb', one_pow, mul_one]

/-- The lift of an evaluation `ψ` with `ψ(f)` a unit to the degree-zero away ring
`(ℤ[X₀,X₁]_f)₀`, via `val` into the full localization and the universal property. -/
private noncomputable def awayLift (f : MvPolynomial (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
    (ψ : MvPolynomial (ULift.{u} (Fin 2)) (ULift.{u} ℤ) →+* B) (hu : IsUnit (ψ f)) :
    Away (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) f →+* B :=
  (IsLocalization.Away.lift (S := Localization.Away f) f hu).comp
    (algebraMap (Away (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) f)
      (Localization.Away f))

/-- **The `awayLift` normal form**: `awayLift ψ (a / fⁿ) · ψ(f)ⁿ = ψ(a)`. -/
private lemma awayLift_mul_eq {f : MvPolynomial (ULift.{u} (Fin 2)) (ULift.{u} ℤ)} {i : ℕ}
    (hf : f ∈ homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ) i)
    (ψ : MvPolynomial (ULift.{u} (Fin 2)) (ULift.{u} ℤ) →+* B) (hu : IsUnit (ψ f)) (n : ℕ)
    (a : MvPolynomial (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
    (ha : a ∈ homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ) (n • i)) :
    awayLift f ψ hu
        (Away.mk (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) hf n a ha)
      * ψ f ^ n = ψ a := by
  have hspec : (Localization.mk a (⟨f ^ n, n, rfl⟩ : Submonoid.powers f))
      * algebraMap _ (Localization.Away f) (f ^ n) = algebraMap _ (Localization.Away f) a := by
    rw [Localization.mk_eq_mk'_apply]
    exact IsLocalization.mk'_spec _ _ _
  have hlift := congrArg (IsLocalization.Away.lift (S := Localization.Away f) f hu) hspec
  rw [map_mul, IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq] at hlift
  calc awayLift f ψ hu
          (Away.mk (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) hf n a ha)
        * ψ f ^ n
      = IsLocalization.Away.lift (S := Localization.Away f) f hu
          (Localization.mk a (⟨f ^ n, n, rfl⟩ : Submonoid.powers f)) * ψ (f ^ n) := by
        rw [awayLift, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
          HomogeneousLocalization.Away.val_mk, map_pow]
    _ = ψ a := hlift

/-- `awayLift` only depends on the evaluation. -/
private lemma awayLift_congr {f : MvPolynomial (ULift.{u} (Fin 2)) (ULift.{u} ℤ)}
    {ψ₁ ψ₂ : MvPolynomial (ULift.{u} (Fin 2)) (ULift.{u} ℤ) →+* B} (h : ψ₁ = ψ₂)
    (hu : IsUnit (ψ₁ f)) :
    awayLift f ψ₁ hu = awayLift f ψ₂ (h ▸ hu) := by
  subst h; rfl

/-- Post-composition with a ring hom commutes with `awayLift`. -/
private lemma comp_awayLift {f : MvPolynomial (ULift.{u} (Fin 2)) (ULift.{u} ℤ)} {i : ℕ}
    (hf : f ∈ homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ) i) (r : B →+* B')
    (ψ : MvPolynomial (ULift.{u} (Fin 2)) (ULift.{u} ℤ) →+* B) (hu : IsUnit (ψ f)) :
    r.comp (awayLift f ψ hu)
      = awayLift f (r.comp ψ) (by simpa using hu.map r) := by
  apply RingHom.ext
  intro w
  obtain ⟨n, a, ha, rfl⟩ :=
    Away.mk_surjective (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) hf w
  have h1 := congrArg r (awayLift_mul_eq hf ψ hu n a ha)
  rw [map_mul, map_pow] at h1
  have h2 := awayLift_mul_eq hf (r.comp ψ) (by simpa using hu.map r) n a ha
  simp only [RingHom.comp_apply] at h2 ⊢
  exact ((hu.map r).pow n).mul_right_cancel (h1.trans h2.symm)

private lemma X0_mem :
    (X ⟨0⟩ : MvPolynomial (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
      ∈ homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ) 1 :=
  ProjTwist.X_mem_deg_one (ULift.{u} (Fin 2)) ⟨0⟩

private lemma X1_mem :
    (X ⟨1⟩ : MvPolynomial (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
      ∈ homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ) 1 :=
  ProjTwist.X_mem_deg_one (ULift.{u} (Fin 2)) ⟨1⟩

/-- The localizing element `X₀X₁` of the overlap chart, as a single opaque constant (keeping
it non-reducible prevents the unifier from re-comparing independently elaborated copies of
the product, which is prohibitively expensive). -/
private noncomputable def X01 : MvPolynomial (ULift.{u} (Fin 2)) (ULift.{u} ℤ) := X ⟨0⟩ * X ⟨1⟩

private lemma X01_eq :
    X01.{u} = (X ⟨0⟩ : MvPolynomial (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) * X ⟨1⟩ := rfl

private lemma X01_eq' :
    X01.{u} = (X ⟨1⟩ : MvPolynomial (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) * X ⟨0⟩ :=
  X01_eq.trans (mul_comm _ _)

private lemma X01_mem :
    X01.{u} ∈ homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ) 2 := by
  rw [X01_eq]
  exact ProjTwist.X_mul_X_mem_deg_two (ULift.{u} (Fin 2)) ⟨0⟩ ⟨1⟩

/-- The classifying ring map of the first chart: `X₀ ↦ 1, X₁ ↦ b` on `(ℤ[X₀,X₁]_{X₀})₀`. -/
private noncomputable def chartHom₀ (b : B) :
    Away (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X ⟨0⟩) →+* B :=
  awayLift (X ⟨0⟩) (p1Eval 1 b) (by rw [p1Eval_X0]; exact isUnit_one)

/-- The classifying ring map of the second chart: `X₀ ↦ b, X₁ ↦ 1` on `(ℤ[X₀,X₁]_{X₁})₀`. -/
private noncomputable def chartHom₁ (b : B) :
    Away (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X ⟨1⟩) →+* B :=
  awayLift (X ⟨1⟩) (p1Eval b 1) (by rw [p1Eval_X1]; exact isUnit_one)

private lemma chartHom₀_mk (b : B) {i : ℕ}
    (hf : (X ⟨0⟩ : MvPolynomial (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
      ∈ homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ) i) (n : ℕ)
    (a : MvPolynomial (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
    (ha : a ∈ homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ) (n • i)) :
    chartHom₀ b (Away.mk (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) hf n a ha)
      = p1Eval 1 b a := by
  have h : chartHom₀ b
        (Away.mk (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) hf n a ha)
      * p1Eval 1 b (X ⟨0⟩) ^ n = p1Eval 1 b a :=
    awayLift_mul_eq hf (p1Eval 1 b) (by rw [p1Eval_X0]; exact isUnit_one) n a ha
  simpa using h

private lemma chartHom₁_mk (b : B) {i : ℕ}
    (hf : (X ⟨1⟩ : MvPolynomial (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
      ∈ homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ) i) (n : ℕ)
    (a : MvPolynomial (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
    (ha : a ∈ homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ) (n • i)) :
    chartHom₁ b (Away.mk (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) hf n a ha)
      = p1Eval b 1 a := by
  have h : chartHom₁ b
        (Away.mk (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) hf n a ha)
      * p1Eval b 1 (X ⟨1⟩) ^ n = p1Eval b 1 a :=
    awayLift_mul_eq hf (p1Eval b 1) (by rw [p1Eval_X1]; exact isUnit_one) n a ha
  simpa using h

/-- Restriction compatibility for the first chart hom. -/
private lemma comp_chartHom₀ (r : B →+* B') (b : B) :
    r.comp (chartHom₀ b) = chartHom₀ (r b) := by
  have heq : r.comp (p1Eval 1 b) = p1Eval 1 (r b) := by rw [comp_p1Eval, map_one]
  exact (comp_awayLift X0_mem r (p1Eval 1 b) (by rw [p1Eval_X0]; exact isUnit_one)).trans
    (awayLift_congr heq _)

/-- Restriction compatibility for the second chart hom. -/
private lemma comp_chartHom₁ (r : B →+* B') (b : B) :
    r.comp (chartHom₁ b) = chartHom₁ (r b) := by
  have heq : r.comp (p1Eval b 1) = p1Eval (r b) 1 := by rw [comp_p1Eval, map_one]
  exact (comp_awayLift X1_mem r (p1Eval b 1) (by rw [p1Eval_X1]; exact isUnit_one)).trans
    (awayLift_congr heq _)

-- The `isDefEq` checks routing the graded instances through the product localizing
-- element `X₀X₁` exceed the default heartbeat budget.
/-- The evaluation `X₀ ↦ 1, X₁ ↦ b` sends `X₀X₁` to the unit `b`. -/
private lemma p1Eval_X01_left (b : B) : p1Eval (B := B) 1 b X01.{u} = b := by
  rw [X01_eq, map_mul, p1Eval_X0, p1Eval_X1, one_mul]

/-- The evaluation `X₀ ↦ b', X₁ ↦ 1` sends `X₀X₁` to the unit `b'`. -/
private lemma p1Eval_X01_right (b' : B) : p1Eval (B := B) b' 1 X01.{u} = b' := by
  rw [X01_eq, map_mul, p1Eval_X0, p1Eval_X1, mul_one]

private lemma isUnit_p1Eval_X01_left (b : B) (hb : IsUnit b) :
    IsUnit (p1Eval (B := B) 1 b X01.{u}) := by
  rw [p1Eval_X01_left]; exact hb

private lemma isUnit_p1Eval_X01_right (b' : B) (hb' : IsUnit b') :
    IsUnit (p1Eval (B := B) b' 1 X01.{u}) := by
  rw [p1Eval_X01_right]; exact hb'

/-- The classifying ring map of the overlap chart, first-chart coordinates:
`X₀ ↦ 1, X₁ ↦ b` on `(ℤ[X₀,X₁]_{X₀X₁})₀`, defined when `b` is a unit. -/
private noncomputable def overlapHom₀ (b : B) (hb : IsUnit b) :
    Away (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) X01.{u} →+* B :=
  awayLift _ (p1Eval 1 b) (isUnit_p1Eval_X01_left b hb)

/-- The classifying ring map of the overlap chart, second-chart coordinates:
`X₀ ↦ b', X₁ ↦ 1` on `(ℤ[X₀,X₁]_{X₀X₁})₀`, defined when `b'` is a unit. -/
private noncomputable def overlapHom₁ (b' : B) (hb' : IsUnit b') :
    Away (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) X01.{u} →+* B :=
  awayLift _ (p1Eval b' 1) (isUnit_p1Eval_X01_right b' hb')

/-- The `awayLift` normal form for the overlap chart, first-chart coordinates. -/
private lemma overlapHom₀_mk (b : B) (hb : IsUnit b) {i : ℕ}
    (hf : X01.{u} ∈ homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ) i) (n : ℕ)
    (a : MvPolynomial (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
    (ha : a ∈ homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ) (n • i)) :
    overlapHom₀ b hb
        (Away.mk (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) hf n a ha)
      * b ^ n = p1Eval 1 b a := by
  have h : overlapHom₀ b hb
        (Away.mk (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) hf n a ha)
      * p1Eval 1 b X01.{u} ^ n = p1Eval 1 b a :=
    awayLift_mul_eq hf (p1Eval 1 b) (isUnit_p1Eval_X01_left b hb) n a ha
  rwa [p1Eval_X01_left] at h

/-- The `awayLift` normal form for the overlap chart, second-chart coordinates. -/
private lemma overlapHom₁_mk (b' : B) (hb' : IsUnit b') {i : ℕ}
    (hf : X01.{u} ∈ homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ) i) (n : ℕ)
    (a : MvPolynomial (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
    (ha : a ∈ homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ) (n • i)) :
    overlapHom₁ b' hb'
        (Away.mk (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) hf n a ha)
      * b' ^ n = p1Eval b' 1 a := by
  have h : overlapHom₁ b' hb'
        (Away.mk (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) hf n a ha)
      * p1Eval b' 1 X01.{u} ^ n = p1Eval b' 1 a :=
    awayLift_mul_eq hf (p1Eval b' 1) (isUnit_p1Eval_X01_right b' hb') n a ha
  rwa [p1Eval_X01_right] at h

set_option maxHeartbeats 1600000 in
-- Heartbeat bump: the final cancellation compares two `Away.mk` normal forms across the
-- `awayMap` transition, an expensive (but convergent) proof-irrelevance `whnf` chain.
/-- The first chart hom factors through the overlap chart hom along the transition map
`(ℤ[X₀,X₁]_{X₀})₀ → (ℤ[X₀,X₁]_{X₀X₁})₀`. -/
private lemma overlapHom₀_comp_awayMap (b : B) (hb : IsUnit b) :
    (overlapHom₀ b hb).comp
        (awayMap (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) X1_mem X01_eq)
      = chartHom₀ b := by
  apply RingHom.ext
  intro w
  obtain ⟨n, a, ha, rfl⟩ :=
    Away.mk_surjective (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) X0_mem w
  rw [RingHom.comp_apply, awayMap_mk, chartHom₀_mk]
  have hmem : a * X ⟨1⟩ ^ n
      ∈ homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ) (n • (1 + 1)) := by
    have h := SetLike.mul_mem_graded ha (SetLike.pow_mem_graded n X1_mem)
    rwa [← smul_add] at h
  have h := overlapHom₀_mk b hb (X01_eq ▸ SetLike.mul_mem_graded X0_mem X1_mem) n
    (a * X ⟨1⟩ ^ n) hmem
  rw [map_mul, map_pow, p1Eval_X1] at h
  exact (hb.pow n).mul_right_cancel h

set_option maxHeartbeats 1600000 in
-- Heartbeat bump: as for `overlapHom₀_comp_awayMap`.
/-- The second chart hom factors through the overlap chart hom along the transition map
`(ℤ[X₀,X₁]_{X₁})₀ → (ℤ[X₀,X₁]_{X₀X₁})₀`. -/
private lemma overlapHom₁_comp_awayMap (b : B) (hb : IsUnit b) :
    (overlapHom₁ b hb).comp
        (awayMap (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) X0_mem X01_eq')
      = chartHom₁ b := by
  apply RingHom.ext
  intro w
  obtain ⟨n, a, ha, rfl⟩ :=
    Away.mk_surjective (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) X1_mem w
  rw [RingHom.comp_apply, awayMap_mk, chartHom₁_mk]
  have hmem : a * X ⟨0⟩ ^ n
      ∈ homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ) (n • (1 + 1)) := by
    have h := SetLike.mul_mem_graded ha (SetLike.pow_mem_graded n X0_mem)
    rwa [← smul_add] at h
  have h := overlapHom₁_mk b hb (X01_eq' ▸ SetLike.mul_mem_graded X1_mem X0_mem) n
    (a * X ⟨0⟩ ^ n) hmem
  rw [map_mul, map_pow, p1Eval_X0] at h
  exact (hb.pow n).mul_right_cancel h

/-- **The overlap agreement**: for a unit pair `b·b' = 1` the two overlap chart homs
coincide (the homogeneous swap identity `p1Eval_swap` after clearing the unit
denominators). -/
private lemma overlapHom₀_eq_overlapHom₁ {b b' : B} (hb : IsUnit b) (hb' : IsUnit b')
    (h : b * b' = 1) : overlapHom₀ b hb = overlapHom₁ b' hb' := by
  apply RingHom.ext
  intro w
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective _ X01_mem w
  have h0 := overlapHom₀_mk b hb X01_mem n a ha
  have h1 := overlapHom₁_mk b' hb' X01_mem n a ha
  have hswap : p1Eval b' 1 a = b' ^ (n • 2) * p1Eval 1 b a :=
    p1Eval_swap h ((mem_homogeneousSubmodule _ _).mp ha)
  have hun : b ^ n * b' ^ n = 1 := by rw [← mul_pow, h, one_pow]
  refine ((hb'.pow n).mul_right_cancel ?_).symm
  rw [h1, hswap, ← h0]
  calc b' ^ (n • 2)
        * (overlapHom₀ b hb (Away.mk _ X01_mem n a ha) * b ^ n)
      = overlapHom₀ b hb (Away.mk _ X01_mem n a ha) * ((b ^ n * b' ^ n) * b' ^ n) := by
        rw [smul_eq_mul, mul_comm n 2, pow_mul, sq]
        ring
    _ = overlapHom₀ b hb (Away.mk _ X01_mem n a ha) * b' ^ n := by
        rw [hun, one_mul]

end ChartHoms

/-! ### The two chart morphisms into `Proj ℤ[X₀,X₁]` and their gluing data

For an open `U` of a scheme `Y` and a section `s ∈ Γ(Y, U)`, the classifying ring maps of
the previous section produce morphisms `U ⟶ Spec (ℤ[X₀,X₁]_{Xᵢ})₀ ⟶ Proj ℤ[X₀,X₁]`
("`s` in the first chart", "`s` in the second chart"), together with their restriction
functoriality, the overlap agreement (through the `D₊(X₀X₁)`-chart), and the chart
preimage computation used for the nonconstancy argument. -/

section ChartMorphisms

open HomogeneousLocalization

variable {Y : Scheme.{u}}

/-- Preimage of a basic open under `Spec.map`. -/
private lemma SpecMap_preimage_basicOpen {R S : CommRingCat.{u}} (φ : R ⟶ S) (r : R) :
    Spec.map φ ⁻¹ᵁ PrimeSpectrum.basicOpen r = PrimeSpectrum.basicOpen (φ.hom r) := by
  ext x
  exact Iff.rfl

/-- The first chart morphism `U ⟶ Proj ℤ[X₀,X₁]` attached to a section `s ∈ Γ(Y, U)`:
classified by `X₀ ↦ 1, X₁ ↦ s` and landing in `D₊(X₀)`. -/
private noncomputable def chartMor₀ (U : Y.Opens) (s : Γ(Y, U)) :
    U.toScheme ⟶ Proj (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) :=
  U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (chartHom₀ s)) ≫
    Proj.awayι (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) _ X0_mem one_pos

/-- The second chart morphism `U ⟶ Proj ℤ[X₀,X₁]` attached to a section `s ∈ Γ(Y, U)`:
classified by `X₀ ↦ s, X₁ ↦ 1` and landing in `D₊(X₁)`. -/
private noncomputable def chartMor₁ (U : Y.Opens) (s : Γ(Y, U)) :
    U.toScheme ⟶ Proj (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) :=
  U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (chartHom₁ s)) ≫
    Proj.awayι (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) _ X1_mem one_pos

/-- The first chart morphism is functorial in restriction. -/
private lemma homOfLE_chartMor₀ {U V : Y.Opens} (h : V ≤ U) (s : Γ(Y, U)) :
    Y.homOfLE h ≫ chartMor₀ U s = chartMor₀ V (Y.presheaf.map (homOfLE h).op s) := by
  rw [chartMor₀, chartMor₀, ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc V U h,
    ← Spec.map_comp_assoc, ← CommRingCat.ofHom_hom (Y.presheaf.map (homOfLE h).op),
    ← CommRingCat.ofHom_comp, comp_chartHom₀]

/-- The second chart morphism is functorial in restriction. -/
private lemma homOfLE_chartMor₁ {U V : Y.Opens} (h : V ≤ U) (s : Γ(Y, U)) :
    Y.homOfLE h ≫ chartMor₁ U s = chartMor₁ V (Y.presheaf.map (homOfLE h).op s) := by
  rw [chartMor₁, chartMor₁, ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc V U h,
    ← Spec.map_comp_assoc, ← CommRingCat.ofHom_hom (Y.presheaf.map (homOfLE h).op),
    ← CommRingCat.ofHom_comp, comp_chartHom₁]

/-- **The overlap agreement of the two chart morphisms.**  If the restrictions of `sU`
and `sV` to `U ⊓ V` multiply to `1`, both chart morphisms restrict to the same morphism
`U ⊓ V ⟶ Proj ℤ[X₀,X₁]`: both factor through the affine chart `D₊(X₀X₁)`, where their
classifying maps agree by the homogeneous swap identity. -/
private lemma chartMor₀_inf_eq_chartMor₁_inf (U V : Y.Opens) (sU : Γ(Y, U)) (sV : Γ(Y, V))
    (h : Y.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op sU
        * Y.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op sV = 1) :
    Y.homOfLE inf_le_left ≫ chartMor₀ U sU
      = Y.homOfLE inf_le_right ≫ chartMor₁ V sV := by
  rw [homOfLE_chartMor₀ inf_le_left sU, homOfLE_chartMor₁ inf_le_right sV]
  set a := Y.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op sU with ha
  set b := Y.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op sV with hb
  have hua : IsUnit a := IsUnit.of_mul_eq_one _ h
  have hub : IsUnit b := IsUnit.of_mul_eq_one _ (by rwa [mul_comm] at h)
  rw [chartMor₀, chartMor₁, ← overlapHom₀_comp_awayMap a hua,
    ← overlapHom₁_comp_awayMap b hub, CommRingCat.ofHom_comp, CommRingCat.ofHom_comp,
    Spec.map_comp, Spec.map_comp]
  simp only [Category.assoc]
  rw [Proj.SpecMap_awayMap_awayι, Proj.SpecMap_awayMap_awayι,
    overlapHom₀_eq_overlapHom₁ hua hub h]

/-- The image of the first chart morphism lies in the basic open `D₊(X₀)`. -/
private lemma chartMor₀_apply_mem (U : Y.Opens) (s : Γ(Y, U)) (w : U.toScheme) :
    chartMor₀ U s w
      ∈ Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X ⟨0⟩) := by
  have hw : chartMor₀ U s w
      = Proj.awayι (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) _ X0_mem one_pos
        (Spec.map (CommRingCat.ofHom (chartHom₀ s)) (U.toSpecΓ w)) := by
    rw [chartMor₀, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  rw [hw, ← Proj.opensRange_awayι _ _ X0_mem one_pos]
  exact Scheme.Hom.mem_opensRange.mpr ⟨_, rfl⟩

/-- **The chart preimage computation.**  The pullback of `D₊(X₀)` along the second chart
morphism of `s` is the non-vanishing locus of `s`. -/
private lemma chartMor₁_preimage_basicOpen (U : Y.Opens) (s : Γ(Y, U)) :
    chartMor₁ U s ⁻¹ᵁ
        Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X ⟨0⟩)
      = U.ι ⁻¹ᵁ Y.basicOpen s := by
  have he : chartHom₁ s (Away.isLocalizationElem X1_mem X0_mem) = s := by
    have h := chartHom₁_mk s X1_mem 1 (X ⟨0⟩ ^ 1) (SetLike.pow_mem_graded 1 X0_mem)
    have h2 : p1Eval (B := Γ(Y, U)) s 1 (X ⟨0⟩ ^ 1) = s := by
      rw [map_pow, p1Eval_X0, pow_one]
    exact h.trans h2
  rw [chartMor₁, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage,
    Proj.awayι_preimage_basicOpen _ X1_mem one_pos X0_mem one_pos,
    SpecMap_preimage_basicOpen, CommRingCat.hom_ofHom, he,
    Scheme.Opens.toSpecΓ_preimage_basicOpen]

/-- Mirror of `chartMor₀_inf_eq_chartMor₁_inf`, with the roles of the two charts
exchanged. -/
private lemma chartMor₁_inf_eq_chartMor₀_inf (U V : Y.Opens) (sU : Γ(Y, U)) (sV : Γ(Y, V))
    (h : Y.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op sU
        * Y.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op sV = 1) :
    Y.homOfLE inf_le_left ≫ chartMor₁ U sU
      = Y.homOfLE inf_le_right ≫ chartMor₀ V sV := by
  rw [homOfLE_chartMor₁ inf_le_left sU, homOfLE_chartMor₀ inf_le_right sV]
  set a := Y.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op sU with ha
  set b := Y.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op sV with hb
  have hua : IsUnit a := IsUnit.of_mul_eq_one _ h
  have hub : IsUnit b := IsUnit.of_mul_eq_one _ (by rwa [mul_comm] at h)
  rw [chartMor₁, chartMor₀, ← overlapHom₁_comp_awayMap a hua,
    ← overlapHom₀_comp_awayMap b hub, CommRingCat.ofHom_comp, CommRingCat.ofHom_comp,
    Spec.map_comp, Spec.map_comp]
  simp only [Category.assoc]
  rw [Proj.SpecMap_awayMap_awayι, Proj.SpecMap_awayMap_awayι,
    overlapHom₀_eq_overlapHom₁ hub hua (by rwa [mul_comm] at h)]

end ChartMorphisms

/-! ### The regularity locus and canonical section of a rational function on the curve -/

section RegLocus

open TopologicalSpace

variable {k : Type u} [Field k]

/-- The AJC curve is an integral scheme (geometric integrality over the one-point base). -/
private instance isIntegral_curve (C : Over (Spec (CommRingCat.of k)))
    [GeometricallyIntegral C.hom] : IsIntegral C.left := by
  haveI : Subsingleton (Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  haveI : IsIntegral (Spec (CommRingCat.of k)) :=
    haveI : IsDomain ↑(CommRingCat.of k) := inferInstanceAs (IsDomain k)
    inferInstance
  exact GeometricallyIntegral.isIntegral_of_subsingleton C.hom

variable (C : Over (Spec (CommRingCat.of k))) [GeometricallyIntegral C.hom]

/-- The stalk-to-function-field map evaluated on a germ is the germ at the generic point. -/
private lemma stalkToFF_germ {U : C.left.Opens} {w : C.left} (hw : w ∈ U) (s : Γ(C.left, U)) :
    algebraMap (C.left.presheaf.stalk w) C.left.functionField
        (C.left.presheaf.germ U w hw s)
      = C.left.presheaf.germ U (genericPoint C.left)
          (((genericPoint_spec C.left).specializes trivial :
              genericPoint C.left ⤳ w).mem_open U.isOpen hw) s := by
  change (C.left.presheaf.stalkSpecializes
      ((genericPoint_spec C.left).specializes trivial)).hom
        (C.left.presheaf.germ U w hw s) = _
  exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _

/-- The index data for the regularity locus of a rational function `t ∈ K(C)`: nonempty
opens `U` carrying a section whose germ at every point of `U` maps to `t` in the function
field. -/
private noncomputable def RegData (t : C.left.functionField) : Type u :=
  {q : Σ U : C.left.Opens, Γ(C.left, U) //
    Nonempty q.1 ∧ ∀ (w : C.left) (hw : w ∈ q.1),
      algebraMap (C.left.presheaf.stalk w) C.left.functionField
        (C.left.presheaf.germ q.1 w hw q.2) = t}

/-- **The regularity locus** of a rational function `t ∈ K(C)`: the (open) locus of
points at whose stalk `t` is regular. -/
private noncomputable def regLocus (t : C.left.functionField) : C.left.Opens :=
  ⨆ i : RegData C t, i.1.1

/-- Membership in the regularity locus is regularity of `t` at the stalk. -/
private lemma mem_regLocus {t : C.left.functionField} {w : C.left} :
    w ∈ regLocus C t
      ↔ t ∈ Set.range (algebraMap (C.left.presheaf.stalk w) C.left.functionField) := by
  constructor
  · intro hw
    obtain ⟨i, hwi⟩ := Opens.mem_iSup.mp hw
    exact ⟨C.left.presheaf.germ i.1.1 w hwi i.1.2, i.2.2 w hwi⟩
  · rintro ⟨g, hg⟩
    obtain ⟨U, hwU, s, hs⟩ := TopCat.Presheaf.exists_germ_eq C.left.presheaf g
    refine Opens.mem_iSup.mpr ⟨⟨⟨U, s⟩, ⟨⟨w, hwU⟩⟩, fun w' hw' => ?_⟩, hwU⟩
    rw [stalkToFF_germ C hw' s, ← hg, ← hs, stalkToFF_germ C hwU s]

/-- The sections of the regularity-locus data are compatible on overlaps: on the (nonempty,
by irreducibility) intersections they have equal germs mapping to `t`, and germs are
injective on the integral curve. -/
private lemma regData_isCompatible (t : C.left.functionField) :
    TopCat.Presheaf.IsCompatible C.left.presheaf (fun i : RegData C t => i.1.1)
      (fun i => i.1.2) := by
  intro i j
  -- the intersection is nonempty since `C` is irreducible
  obtain ⟨wi⟩ := i.2.1
  obtain ⟨wj⟩ := j.2.1
  obtain ⟨w, hw⟩ : ∃ w, w ∈ (i.1.1 : Set C.left) ∩ j.1.1 := by
    have h := (PreirreducibleSpace.isPreirreducible_univ (X := C.left))
      i.1.1.1 j.1.1.1 i.1.1.2 j.1.1.2 ⟨wi.1, Set.mem_univ _, wi.2⟩ ⟨wj.1, Set.mem_univ _, wj.2⟩
    obtain ⟨w, -, hw⟩ := h
    exact ⟨w, hw⟩
  have hwi : w ∈ i.1.1 ⊓ j.1.1 := hw
  apply germ_injective_of_isIntegral C.left w hwi
  rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
  apply IsFractionRing.injective (C.left.presheaf.stalk w) C.left.functionField
  rw [i.2.2 w, j.2.2 w]

/-- **The canonical section of `t` on its regularity locus**, glued by the sheaf axiom. -/
private noncomputable def regSection (t : C.left.functionField) :
    Γ(C.left, regLocus C t) :=
  (C.left.sheaf.existsUnique_gluing' (fun i : RegData C t => i.1.1) (regLocus C t)
    (fun i => homOfLE (le_iSup (fun i : RegData C t => i.1.1) i)) le_rfl (fun i => i.1.2)
    (regData_isCompatible C t)).exists.choose

/-- The canonical section maps to `t` at every point of the regularity locus. -/
private lemma regSection_spec (t : C.left.functionField) (w : C.left)
    (hw : w ∈ regLocus C t) :
    algebraMap (C.left.presheaf.stalk w) C.left.functionField
      (C.left.presheaf.germ (regLocus C t) w hw (regSection C t)) = t := by
  obtain ⟨i, hwi⟩ := Opens.mem_iSup.mp hw
  have hres : C.left.presheaf.map
        (homOfLE (le_iSup (fun i : RegData C t => i.1.1) i)).op (regSection C t) = i.1.2 :=
    (C.left.sheaf.existsUnique_gluing' (fun i : RegData C t => i.1.1)
      (regLocus C t) (fun i => homOfLE (le_iSup (fun i : RegData C t => i.1.1) i)) le_rfl
      (fun i => i.1.2) (regData_isCompatible C t)).exists.choose_spec i
  have hg : C.left.presheaf.germ (regLocus C t) w hw (regSection C t)
      = C.left.presheaf.germ i.1.1 w hwi i.1.2 := by
    rw [← hres]
    exact (TopCat.Presheaf.germ_res_apply C.left.presheaf
      (homOfLE (le_iSup (fun j : RegData C t => j.1.1) i)) w hwi (regSection C t)).symm
  rw [hg]
  exact i.2.2 w hwi

/-- The generic point lies in every regularity locus. -/
private lemma genericPoint_mem_regLocus (t : C.left.functionField) :
    genericPoint C.left ∈ regLocus C t := by
  rw [mem_regLocus]
  refine ⟨t, ?_⟩
  change (C.left.presheaf.stalkSpecializes
      ((genericPoint_spec C.left).specializes trivial)).hom t = t
  have h1 : C.left.presheaf.stalkSpecializes
      ((genericPoint_spec C.left).specializes trivial)
      = 𝟙 (C.left.presheaf.stalk (genericPoint C.left)) :=
    C.left.presheaf.stalkSpecializes_refl (genericPoint C.left)
  rw [h1]
  rfl

/-- At the generic point, the germ of the canonical section *is* the rational function
(the stalk at the generic point is the function field, via the identity
specialization map). -/
private lemma germ_regSection_genericPoint (t : C.left.functionField) :
    C.left.presheaf.germ (regLocus C t) (genericPoint C.left)
      (genericPoint_mem_regLocus C t) (regSection C t) = t := by
  have h := regSection_spec C t (genericPoint C.left) (genericPoint_mem_regLocus C t)
  have hid : C.left.presheaf.stalkSpecializes
      ((genericPoint_spec C.left).specializes (Set.mem_univ (genericPoint C.left)))
      = 𝟙 (C.left.presheaf.stalk (genericPoint C.left)) :=
    C.left.presheaf.stalkSpecializes_refl (genericPoint C.left)
  have h2 : (C.left.presheaf.stalkSpecializes
      ((genericPoint_spec C.left).specializes (Set.mem_univ (genericPoint C.left)))).hom
        (C.left.presheaf.germ (regLocus C t) (genericPoint C.left)
          (genericPoint_mem_regLocus C t) (regSection C t)) = t := h
  rw [hid] at h2
  simpa using h2

/-- **Existence of a rational function with a pole.**  The curve has a non-generic point
`x`; its stalk is a local domain of positive dimension, so for `0 ≠ π ∈ 𝔪ₓ` the rational
function `t = π⁻¹ ∈ K(C)` is nonzero, fails to be regular at `x`, and has regular
inverse at `x`. -/
private lemma exists_pole [SmoothOfRelativeDimension 1 C.hom] :
    ∃ (t : C.left.functionField) (x : C.left), t ≠ 0
      ∧ t ∉ Set.range (algebraMap (C.left.presheaf.stalk x) C.left.functionField)
      ∧ t⁻¹ ∈ Set.range (algebraMap (C.left.presheaf.stalk x) C.left.functionField) := by
  -- a point different from the generic point, via the height lower bound on a chart
  obtain ⟨x, hxne⟩ : ∃ x : C.left, x ≠ genericPoint C.left := by
    obtain ⟨z⟩ : Nonempty C.left := inferInstance
    obtain ⟨U, hU, V, hV, hzV, e, hss⟩ :=
      SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
        (n := 1) (f := C.hom) z
    haveI : Subsingleton (Spec (CommRingCat.of k)) :=
      inferInstanceAs (Subsingleton (PrimeSpectrum k))
    have hUtop : U = ⊤ := by
      refine top_le_iff.mp fun y _ => ?_
      rw [Subsingleton.elim y (C.hom.base z)]
      exact e hzV
    subst hUtop
    let eΓ : Γ(Spec (CommRingCat.of k), ⊤) ≃+* k :=
      (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
    have hφss : RingHom.IsStandardSmoothOfRelativeDimension 1
        ((C.hom.appLE ⊤ V e).hom.comp eΓ.symm.toRingHom) :=
      (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := 1)).right _ eΓ.symm hss
    letI : Algebra k Γ(C.left, V) :=
      ((C.hom.appLE ⊤ V e).hom.comp eΓ.symm.toRingHom).toAlgebra
    haveI : Algebra.IsStandardSmoothOfRelativeDimension 1 k Γ(C.left, V) := hφss.toAlgebra
    haveI : Nonempty V := ⟨⟨z, hzV⟩⟩
    obtain ⟨m, hm⟩ := Ideal.exists_maximal Γ(C.left, V)
    haveI := hm.isPrime
    have h1 : (1 : ℕ∞) ≤ m.height := by
      exact_mod_cast
        Algebra.IsStandardSmoothOfRelativeDimension.natCast_le_height_of_isMaximal
          (k := k) 1 m hm
    -- extract a strictly smaller prime from the positive height
    have hnm : ¬ IsMin (⟨m, hm.isPrime⟩ : PrimeSpectrum Γ(C.left, V)) := by
      intro hmin
      have h2 : (1 : ℕ∞) ≤ Order.height (⟨m, hm.isPrime⟩ : PrimeSpectrum Γ(C.left, V)) := by
        rw [← PrimeSpectrum.height_eq_orderHeight]
        exact h1
      rw [Order.height_eq_zero.mpr hmin] at h2
      simp at h2
    obtain ⟨q, hq⟩ := not_isMin_iff.mp hnm
    have hinj : Function.Injective hV.fromSpec := hV.fromSpec.isOpenEmbedding.injective
    have hne : hV.fromSpec q ≠ hV.fromSpec ⟨m, hm.isPrime⟩ :=
      fun hEq => (ne_of_lt hq) (hinj hEq)
    rcases eq_or_ne (hV.fromSpec q) (genericPoint C.left) with hgen | hgen
    · exact ⟨hV.fromSpec ⟨m, hm.isPrime⟩, fun hh => hne (by rw [hgen, hh])⟩
    · exact ⟨hV.fromSpec q, hgen⟩
  -- the stalk at `x` has nonzero maximal ideal
  have h2 : genericPoint C.left ⤳ x := genericPoint_specializes x
  have hlt : x < genericPoint C.left := lt_iff_le_not_ge.mpr
    ⟨h2, fun h => hxne ((show x ⤳ genericPoint C.left from h).antisymm h2).eq⟩
  have hcoh : (1 : ℕ∞) ≤ Order.coheight x :=
    le_trans le_add_self (Order.coheight_add_one_le hlt)
  have hnf : ¬ IsField (C.left.presheaf.stalk x) := by
    intro hF
    have h0 : ringKrullDim (C.left.presheaf.stalk x) = 0 := ringKrullDim_eq_zero_of_isField hF
    rw [Scheme.ringKrullDim_stalk_eq_coheight] at h0
    have hc0 : Order.coheight x = 0 := by exact_mod_cast h0
    rw [hc0] at hcoh
    simp at hcoh
  have hmne : IsLocalRing.maximalIdeal (C.left.presheaf.stalk x) ≠ ⊥ :=
    fun h => hnf (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h)
  obtain ⟨π, hπm, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hmne
  have hπK : algebraMap (C.left.presheaf.stalk x) C.left.functionField π ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ C.left.functionField)).mpr hπ0
  refine ⟨(algebraMap (C.left.presheaf.stalk x) C.left.functionField π)⁻¹, x,
    inv_ne_zero hπK, ?_, ?_⟩
  · rintro ⟨b, hb⟩
    have h1 : algebraMap (C.left.presheaf.stalk x) C.left.functionField (b * π) = 1 := by
      rw [map_mul, hb, inv_mul_cancel₀ hπK]
    have hbπ : b * π = 1 := by
      apply IsFractionRing.injective (C.left.presheaf.stalk x) C.left.functionField
      rw [h1, map_one]
    have hu : IsUnit π := IsUnit.of_mul_eq_one _ (by rwa [mul_comm] at hbπ)
    exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal π).mp hπm) hu
  · exact ⟨π, by rw [inv_inv]⟩

end RegLocus


/-! ### The valuative dichotomy and the glued nonconstant morphism to `Proj ℤ[X₀,X₁]` -/

section GateDischarge

open TopologicalSpace

variable {k : Type u} [Field k]

/-- **The valuative dichotomy on the AJC curve (arbitrary base field).**
Every nonzero rational function is, at every point, either regular or has regular
inverse: `L(t) ∪ L(t⁻¹) = C`.  At a non-generic point `w` this descends, by faithful
flatness of the stalk map, from the same dichotomy in the DVR stalk of the base change
`C_{k̄}` at a point over `w` (`Scheme.localRing_dvr_of_codim_one` over the algebraic
closure). -/
private lemma regLocus_sup_regLocus_inv_eq_top
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIntegral C.hom]
    {t : C.left.functionField} (ht : t ≠ 0) :
    regLocus C t ⊔ regLocus C t⁻¹ = ⊤ := by
  haveI : Smooth C.hom := SmoothOfRelativeDimension.smooth 1 C.hom
  rw [eq_top_iff]
  rintro w -
  rw [Opens.mem_sup]
  -- the base change to the algebraic closure and its projection
  haveI : Subsingleton (Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  haveI : Nonempty (Spec (CommRingCat.of (AlgebraicClosure k))) :=
    inferInstanceAs (Nonempty (PrimeSpectrum (AlgebraicClosure k)))
  set y : Spec (CommRingCat.of (AlgebraicClosure k)) ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))) with hy
  haveI : Surjective y := ⟨fun _ => ⟨Nonempty.some ‹_›, Subsingleton.elim _ _⟩⟩
  haveI : Flat y := by
    rw [hy, AlgebraicGeometry.Flat.SpecMap_iff, CommRingCat.hom_ofHom,
      RingHom.flat_algebraMap_iff]
    infer_instance
  set p := pullback.fst C.hom y with hp
  haveI : Surjective p := by rw [hp]; infer_instance
  haveI : Flat p := by rw [hp]; infer_instance
  obtain ⟨z', rfl⟩ := p.surjective w
  rw [mem_regLocus, mem_regLocus]
  by_cases hgen : p z' = genericPoint C.left
  · left
    rw [hgen]
    exact (mem_regLocus C).mp (genericPoint_mem_regLocus C t)
  · -- ambient instances on the base-changed curve
    haveI hCbInt : IsIntegral (pullback C.hom y) :=
      GeometricallyIntegral.geometrically_isIntegral (f := C.hom) y
        (pullback.fst C.hom y) (pullback.snd C.hom y) (IsPullback.of_hasPullback C.hom y)
    haveI : IsIntegral (Over.mk (pullback.snd C.hom y)).left := hCbInt
    haveI : IsReduced (Over.mk (pullback.snd C.hom y)).left :=
      inferInstanceAs (IsReduced (pullback C.hom y))
    haveI : Smooth (Over.mk (pullback.snd C.hom y)).hom :=
      MorphismProperty.pullback_snd _ _ ‹Smooth C.hom›
    haveI : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension 1) :=
      smoothOfRelativeDimension_isStableUnderBaseChange 1
    haveI : SmoothOfRelativeDimension 1 (Over.mk (pullback.snd C.hom y)).hom :=
      MorphismProperty.pullback_snd _ _ ‹SmoothOfRelativeDimension 1 C.hom›
    haveI : GeometricallyIrreducible (Over.mk (pullback.snd C.hom y)).hom :=
      MorphismProperty.pullback_snd _ _ (inferInstance : GeometricallyIrreducible C.hom)
    haveI : IsSeparated (Over.mk (pullback.snd C.hom y)).hom :=
      MorphismProperty.pullback_snd _ _ (inferInstance : IsSeparated C.hom)
    haveI : LocallyOfFiniteType (Over.mk (pullback.snd C.hom y)).hom :=
      MorphismProperty.pullback_snd _ _ (inferInstance : LocallyOfFiniteType C.hom)
    -- the faithfully flat local stalk map at `z'`
    have hφflat : ((p.stalkMap z').hom).Flat := AlgebraicGeometry.Flat.stalkMap p z'
    letI : Algebra (C.left.presheaf.stalk (p z'))
        ((pullback C.hom y).presheaf.stalk z') := ((p.stalkMap z').hom).toAlgebra
    haveI : Module.Flat (C.left.presheaf.stalk (p z'))
        ((pullback C.hom y).presheaf.stalk z') := hφflat
    haveI : IsLocalHom (algebraMap (C.left.presheaf.stalk (p z'))
        ((pullback C.hom y).presheaf.stalk z')) :=
      inferInstanceAs (IsLocalHom ((p.stalkMap z').hom))
    haveI : Module.FaithfullyFlat (C.left.presheaf.stalk (p z'))
        ((pullback C.hom y).presheaf.stalk z') :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    -- the source stalk is not a field: pick `0 ≠ π` in its maximal ideal
    have h2 : genericPoint C.left ⤳ p z' := genericPoint_specializes _
    have hlt : p z' < genericPoint C.left := lt_iff_le_not_ge.mpr
      ⟨h2, fun h => hgen ((show p z' ⤳ genericPoint C.left from h).antisymm h2).eq⟩
    have hcohA : (1 : ℕ∞) ≤ Order.coheight (p z') :=
      le_trans le_add_self (Order.coheight_add_one_le hlt)
    have hnfA : ¬ IsField (C.left.presheaf.stalk (p z')) := by
      intro hF
      have h0 : ringKrullDim (C.left.presheaf.stalk (p z')) = 0 :=
        ringKrullDim_eq_zero_of_isField hF
      rw [Scheme.ringKrullDim_stalk_eq_coheight] at h0
      have hc0 : Order.coheight (p z') = 0 := by exact_mod_cast h0
      rw [hc0] at hcohA
      simp at hcohA
    have hmA : IsLocalRing.maximalIdeal (C.left.presheaf.stalk (p z')) ≠ ⊥ :=
      fun h => hnfA (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h)
    obtain ⟨π, hπm, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hmA
    have hπB0 : (p.stalkMap z').hom π ≠ 0 := fun h0 =>
      hπ0 (FaithfulSMul.algebraMap_injective (C.left.presheaf.stalk (p z'))
        ((pullback C.hom y).presheaf.stalk z')
        (show algebraMap _ _ π = algebraMap _ _ 0 by rw [map_zero]; exact h0))
    have hπBm : (p.stalkMap z').hom π ∈
        IsLocalRing.maximalIdeal ((pullback C.hom y).presheaf.stalk z') := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal π).mp hπm)
        (isUnit_of_map_unit ((p.stalkMap z').hom) π hu)
    have hmB : IsLocalRing.maximalIdeal ((pullback C.hom y).presheaf.stalk z') ≠ ⊥ := by
      intro hbot
      rw [hbot] at hπBm
      exact hπB0 (Submodule.mem_bot _ |>.mp hπBm)
    -- the target stalk is a codimension-one DVR
    have hcohB : Order.coheight z' = 1 := by
      have hle := coheight_le_one_of_curve (Over.mk (pullback.snd C.hom y)) z'
      have hne0 : Order.coheight z' ≠ 0 := by
        intro h0
        have hdim0 : ringKrullDim ((pullback C.hom y).presheaf.stalk z') = 0 := by
          rw [Scheme.ringKrullDim_stalk_eq_coheight, h0]
          rfl
        haveI : Ring.KrullDimLE 0 ((pullback C.hom y).presheaf.stalk z') :=
          Ring.krullDimLE_iff.mpr (le_of_eq hdim0)
        have hbotmax : (⊥ : Ideal ((pullback C.hom y).presheaf.stalk z')).IsMaximal :=
          Ideal.isPrime_bot.isMaximal'
        exact hmB (IsLocalRing.eq_maximalIdeal hbotmax).symm
      exact le_antisymm hle (Order.one_le_iff_ne_zero.mpr hne0)
    have hDVR : IsDiscreteValuationRing ((pullback C.hom y).presheaf.stalk z') :=
      Scheme.localRing_dvr_of_codim_one (X := Over.mk (pullback.snd C.hom y)) z' hcohB
    haveI := hDVR
    haveI : ValuationRing ((pullback C.hom y).presheaf.stalk z') := inferInstance
    -- descend the valuation dichotomy along the faithfully flat stalk map
    exact mem_range_algebraMap_or_inv_mem_range
      (B := (((pullback C.hom y).presheaf.stalk z' : CommRingCat) : Type u))
      (L := FractionRing (((pullback C.hom y).presheaf.stalk z' : CommRingCat) : Type u))
      t ht

/-- **Discharging the residual gate (node `N9a`): the AJC curve admits a nonconstant
morphism to `Proj ℤ[X₀, X₁]`.**  The two chart morphisms attached to a rational function
with a pole (`exists_pole`) glue over the cover `L(t) ∪ L(t⁻¹) = C` given by the
valuative dichotomy, and the glued morphism separates the generic point (which lands in
`D₊(X₀)`) from the pole (which does not). -/
instance existsNonconstantMapToProjInt_of_ajc
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIntegral C.hom] :
    ExistsNonconstantMapToProjInt C := by
  constructor
  obtain ⟨t, x, ht0, hpole, hinvreg⟩ := exists_pole C
  have hx₁ : x ∈ regLocus C t⁻¹ := (mem_regLocus C).mpr hinvreg
  have hη₀ : genericPoint C.left ∈ regLocus C t := genericPoint_mem_regLocus C t
  have hη₁ : genericPoint C.left ∈ regLocus C t⁻¹ := genericPoint_mem_regLocus C t⁻¹
  -- the product of the restricted canonical sections is 1 on the overlap
  have hprod : C.left.presheaf.map
        (homOfLE (inf_le_left : regLocus C t ⊓ regLocus C t⁻¹ ≤ regLocus C t)).op
        (regSection C t)
      * C.left.presheaf.map
        (homOfLE (inf_le_right : regLocus C t ⊓ regLocus C t⁻¹ ≤ regLocus C t⁻¹)).op
        (regSection C t⁻¹) = 1 := by
    apply germ_injective_of_isIntegral C.left (genericPoint C.left)
      (⟨hη₀, hη₁⟩ : genericPoint C.left ∈ regLocus C t ⊓ regLocus C t⁻¹)
    rw [map_mul, map_one, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
    refine Eq.trans ?_ (mul_inv_cancel₀ ht0)
    congr 1
    · exact germ_regSection_genericPoint C t
    · exact germ_regSection_genericPoint C t⁻¹
  -- the two-chart open cover
  have hsup : (⨆ b : ULift.{u} Bool,
      bif b.down then regLocus C t else regLocus C t⁻¹) = ⊤ := by
    rw [eq_top_iff, ← regLocus_sup_regLocus_inv_eq_top C ht0]
    exact sup_le
      (le_iSup (fun b : ULift.{u} Bool =>
        bif b.down then regLocus C t else regLocus C t⁻¹) ⟨true⟩)
      (le_iSup (fun b : ULift.{u} Bool =>
        bif b.down then regLocus C t else regLocus C t⁻¹) ⟨false⟩)
  have hpb := isPullback_opens_inf (regLocus C t) (regLocus C t⁻¹)
  have hpb' := isPullback_opens_inf (regLocus C t⁻¹) (regLocus C t)
  -- the chart morphisms over the cover
  let fam : ∀ b : ULift.{u} Bool,
      ((bif b.down then regLocus C t else regLocus C t⁻¹ : C.left.Opens) : C.left.Opens).toScheme
        ⟶ Proj (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) :=
    fun b => match b with
      | ⟨true⟩ => chartMor₀ (regLocus C t) (regSection C t)
      | ⟨false⟩ => chartMor₁ (regLocus C t⁻¹) (regSection C t⁻¹)
  have hcompat : ∀ b b' : ULift.{u} Bool,
      pullback.fst ((C.left.openCoverOfIsOpenCover _ hsup).f b)
          ((C.left.openCoverOfIsOpenCover _ hsup).f b') ≫ fam b
        = pullback.snd _ _ ≫ fam b' := by
    rintro ⟨b⟩ ⟨b'⟩
    cases b <;> cases b'
    · -- (false, false): the diagonal case
      change pullback.fst ((regLocus C t⁻¹).ι) ((regLocus C t⁻¹).ι)
          ≫ chartMor₁ (regLocus C t⁻¹) (regSection C t⁻¹)
        = pullback.snd ((regLocus C t⁻¹).ι) ((regLocus C t⁻¹).ι)
          ≫ chartMor₁ (regLocus C t⁻¹) (regSection C t⁻¹)
      have hfs : pullback.fst ((regLocus C t⁻¹).ι) ((regLocus C t⁻¹).ι)
          = pullback.snd ((regLocus C t⁻¹).ι) ((regLocus C t⁻¹).ι) := by
        rw [← cancel_mono ((regLocus C t⁻¹).ι)]
        exact pullback.condition
      rw [hfs]
    · -- (false, true): mirrored overlap agreement
      change pullback.fst ((regLocus C t⁻¹).ι) ((regLocus C t).ι)
          ≫ chartMor₁ (regLocus C t⁻¹) (regSection C t⁻¹)
        = pullback.snd ((regLocus C t⁻¹).ι) ((regLocus C t).ι)
          ≫ chartMor₀ (regLocus C t) (regSection C t)
      rw [← cancel_epi hpb'.isoPullback.hom, ← Category.assoc, ← Category.assoc,
        hpb'.isoPullback_hom_fst, hpb'.isoPullback_hom_snd]
      apply chartMor₁_inf_eq_chartMor₀_inf
      -- the product on `L₁ ⊓ L₀`, from `hprod` by commutativity of the intersection
      apply germ_injective_of_isIntegral C.left (genericPoint C.left)
        (⟨hη₁, hη₀⟩ : genericPoint C.left ∈ regLocus C t⁻¹ ⊓ regLocus C t)
      rw [map_mul, map_one, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
      refine Eq.trans ?_ (inv_mul_cancel₀ ht0)
      congr 1
      · exact germ_regSection_genericPoint C t⁻¹
      · exact germ_regSection_genericPoint C t
    · -- (true, false): the overlap agreement
      change pullback.fst ((regLocus C t).ι) ((regLocus C t⁻¹).ι)
          ≫ chartMor₀ (regLocus C t) (regSection C t)
        = pullback.snd ((regLocus C t).ι) ((regLocus C t⁻¹).ι)
          ≫ chartMor₁ (regLocus C t⁻¹) (regSection C t⁻¹)
      rw [← cancel_epi hpb.isoPullback.hom, ← Category.assoc, ← Category.assoc,
        hpb.isoPullback_hom_fst, hpb.isoPullback_hom_snd]
      exact chartMor₀_inf_eq_chartMor₁_inf _ _ _ _ hprod
    · -- (true, true): the diagonal case
      change pullback.fst ((regLocus C t).ι) ((regLocus C t).ι)
          ≫ chartMor₀ (regLocus C t) (regSection C t)
        = pullback.snd ((regLocus C t).ι) ((regLocus C t).ι)
          ≫ chartMor₀ (regLocus C t) (regSection C t)
      have hfs : pullback.fst ((regLocus C t).ι) ((regLocus C t).ι)
          = pullback.snd ((regLocus C t).ι) ((regLocus C t).ι) := by
        rw [← cancel_mono ((regLocus C t).ι)]
        exact pullback.condition
      rw [hfs]
  -- glue
  set f := (C.left.openCoverOfIsOpenCover _ hsup).glueMorphisms fam hcompat with hf
  have h0 : (regLocus C t).ι ≫ f = chartMor₀ (regLocus C t) (regSection C t) := by
    have h := Scheme.Cover.ι_glueMorphisms
      (C.left.openCoverOfIsOpenCover _ hsup) fam hcompat (⟨true⟩ : ULift.{u} Bool)
    rw [Scheme.openCoverOfIsOpenCover_f] at h
    exact h
  have h1 : (regLocus C t⁻¹).ι ≫ f = chartMor₁ (regLocus C t⁻¹) (regSection C t⁻¹) := by
    have h := Scheme.Cover.ι_glueMorphisms
      (C.left.openCoverOfIsOpenCover _ hsup) fam hcompat (⟨false⟩ : ULift.{u} Bool)
    rw [Scheme.openCoverOfIsOpenCover_f] at h
    exact h
  -- point images
  have hfη : f (genericPoint C.left)
      = chartMor₀ (regLocus C t) (regSection C t) ⟨genericPoint C.left, hη₀⟩ := by
    have happ := congrArg
      (fun g : ((regLocus C t : C.left.Opens).toScheme ⟶
        Proj (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))) =>
          g ⟨genericPoint C.left, hη₀⟩) h0
    simp only at happ
    rw [Scheme.Hom.comp_apply] at happ
    exact happ
  have hfx : f x
      = chartMor₁ (regLocus C t⁻¹) (regSection C t⁻¹) ⟨x, hx₁⟩ := by
    have happ := congrArg
      (fun g : ((regLocus C t⁻¹ : C.left.Opens).toScheme ⟶
        Proj (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))) =>
          g ⟨x, hx₁⟩) h1
    simp only at happ
    rw [Scheme.Hom.comp_apply] at happ
    exact happ
  -- the generic point lands in `D₊(X₀)` …
  have hmem₀ : f (genericPoint C.left)
      ∈ Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X ⟨0⟩) := by
    rw [hfη]
    exact chartMor₀_apply_mem _ _ _
  -- … while the pole does not
  have hmem₁ : f x
      ∉ Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X ⟨0⟩) := by
    rw [hfx]
    intro hmem
    have hpre : (⟨x, hx₁⟩ : ↥(regLocus C t⁻¹ : C.left.Opens))
        ∈ chartMor₁ (regLocus C t⁻¹) (regSection C t⁻¹) ⁻¹ᵁ
          Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
            (X ⟨0⟩) := hmem
    rw [chartMor₁_preimage_basicOpen] at hpre
    have hxb : x ∈ C.left.basicOpen (regSection C t⁻¹) := hpre
    obtain ⟨u, hu⟩ := (Scheme.mem_basicOpen C.left (regSection C t⁻¹) x hx₁).mp hxb
    have hgerm : algebraMap (C.left.presheaf.stalk x) C.left.functionField
        (C.left.presheaf.germ (regLocus C t⁻¹) x hx₁ (regSection C t⁻¹)) = t⁻¹ :=
      regSection_spec C t⁻¹ x hx₁
    apply hpole
    refine ⟨↑u⁻¹, ?_⟩
    have hmul : ((↑u⁻¹ : C.left.presheaf.stalk x))
        * C.left.presheaf.germ (regLocus C t⁻¹) x hx₁ (regSection C t⁻¹) = 1 := by
      rw [← hu, Units.inv_mul]
    have hK := congrArg
      (algebraMap (C.left.presheaf.stalk x) C.left.functionField) hmul
    rw [map_mul, map_one, hgerm] at hK
    calc algebraMap (C.left.presheaf.stalk x) C.left.functionField ↑u⁻¹
        = algebraMap (C.left.presheaf.stalk x) C.left.functionField ↑u⁻¹ * t⁻¹ * t := by
          rw [mul_assoc, inv_mul_cancel₀ ht0, mul_one]
      _ = t := by rw [hK, one_mul]
  exact ⟨f, genericPoint C.left, x, fun hEq => hmem₁ (hEq ▸ hmem₀)⟩

end GateDischarge

end AlgebraicGeometry.Adelic
