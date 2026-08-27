/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RingTheory.Polynomial.HilbertPoly
import AlgebraicJacobian.Picard.SectionGradedRing
import AlgebraicJacobian.Picard.GradedHilbertSerre

/-!
# The Hilbert polynomial of a coherent sheaf along a fibre (Nitsure §1)

This file gives the **real definition** of the Hilbert polynomial
`AlgebraicGeometry.Scheme.hilbertPolynomial` of a sheaf of modules `F` on
`X ⟶ S` at a point `s : S` relative to a line bundle `L`, via the graded
Hilbert function of the fibre section module — the `H⁰`-only encoding pinned
in the blueprint (`def:hilbert_polynomial`,
`blueprint/src/chapters/Picard_QuotScheme.tex`):

* the fibre `X_s = π.fiber s` is Mathlib's scheme-theoretic fibre
  `pullback π (S.fromSpecResidueField s)`;
* the restrictions `F_s`, `L_s` are the module pullbacks along the fibre
  embedding `π.fiberι s` (`Scheme.Hom.fiberModule`);
* the twists `F_s ⊗ L_s^{⊗m}` are `Scheme.Modules.moduleTensorPow` of
  `AlgebraicJacobian.Picard.SectionGradedRing`;
* their global sections are `κ(s)`-vector spaces via the structural ring
  homomorphism `κ(s) →+* Γ(X_s, 𝒪)` (`Scheme.Hom.fiberResidueMap`,
  `Scheme.Hom.fiberSectionsModule`), giving the graded Hilbert function
  `m ↦ dim_{κ(s)} Γ(X_s, F_s ⊗ L_s^{⊗m})` (`Scheme.hilbertFunction`);
* `Scheme.hilbertPolynomial π L F s` is the unique `Φ ∈ ℚ[λ]` that agrees
  with the graded Hilbert function for all `m ≫ 0` when such a polynomial
  exists, and the junk value `0` otherwise.  Whenever the eventual-match
  condition holds the polynomial is unique (two rational polynomials agreeing
  at all large naturals are equal), so the classical-choice extraction is
  canonical; no numerical invariant is lost (see the Serre-vanishing
  discussion in `def:hilbert_polynomial`).

The bridge from the graded Hilbert–Serre rationality engine is
`Scheme.existsUnique_hilbertPolynomial_of_isRatHilb`: when the graded Hilbert
function is a rational Hilbert function (`AlgebraicGeometry.IsRatHilb`, the
output shape of `AlgebraicGeometry.gradedModule_hilbertSeries_rational`), the
eventual-match condition holds, the matching polynomial is unique, and
`hilbertPolynomial` computes it (`Scheme.hilbertPolynomial_eq_hilbertPoly`).
Producing the `IsRatHilb` hypothesis for proper `X_s` and ample `L_s` is the
finite-generation theorem `lem:sectionGradedModule_fg` (Serre), which is
future work; it enters only through the lemmas here, never through the
definition of `hilbertPolynomial` itself.

Blueprint: `def:hilbert_polynomial`, `sec:graded_hilbert_polynomial`
(`blueprint/src/chapters/Picard_QuotScheme.tex`).
Source: [Nitsure], §1, sub-section "Stratification by Hilbert Polynomials"
(`references/nitsure-hilbert-quot-src/nitsure-hilbert-quot.tex`, L453–L478);
cf. [Hartshorne], III.5.2.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme

variable {S X : Scheme.{u}}

/-- The restriction `F_s = F|_{X_s}` of a sheaf of modules `F` on `X` to the
scheme-theoretic fibre `X_s = π.fiber s` of `π : X ⟶ S` over `s : S`: the
module pullback along the fibre embedding `π.fiberι s : π.fiber s ⟶ X`.
Blueprint: the restriction `F_s` of `def:hilbert_polynomial`. -/
noncomputable def Hom.fiberModule (π : X ⟶ S) (s : S) (F : X.Modules) :
    (π.fiber s).Modules :=
  (Scheme.Modules.pullback (π.fiberι s)).obj F

/-- The structural ring homomorphism `κ(s) ⟶ Γ(X_s, 𝒪_{X_s})` of the fibre
`X_s = π.fiber s`: global sections of the structural morphism
`π.fiberToSpecResidueField s : X_s ⟶ Spec κ(s)`, transported along the
canonical isomorphism `Γ(Spec κ(s), ⊤) ≅ κ(s)`.  It makes every section
module of a sheaf of modules on the fibre a `κ(s)`-vector space
(`Scheme.Hom.fiberSectionsModule`). -/
noncomputable def Hom.fiberResidueMap (π : X ⟶ S) (s : S) :
    S.residueField s ⟶ Γ(π.fiber s, ⊤) :=
  (Scheme.ΓSpecIso (S.residueField s)).inv ≫ (π.fiberToSpecResidueField s).appTop

/-- The `κ(s)`-module structure on the global sections of a sheaf of modules
`G` on the fibre `X_s = π.fiber s`: restriction of scalars along the
structural ring homomorphism `κ(s) →+* Γ(X_s, 𝒪)`
(`Scheme.Hom.fiberResidueMap`).  Not an instance (the fibre presentation of
the scheme is not canonical); brought into scope with `letI` at use sites. -/
@[reducible] noncomputable def Hom.fiberSectionsModule (π : X ⟶ S) (s : S)
    (G : (π.fiber s).Modules) :
    Module (S.residueField s) Γ(G, ⊤) :=
  Module.compHom Γ(G, ⊤) (π.fiberResidueMap s).hom

/-- The **graded Hilbert function** of `F` at the fibre over `s : S`, relative
to the line bundle `L`:

`m ↦ dim_{κ(s)} Γ(X_s, F_s ⊗ L_s^{⊗m})`,

the dimension over the residue field `κ(s)` of the global sections of the
`m`-th twist of the restriction `F_s` by `L_s` on the scheme-theoretic fibre
`X_s = π.fiber s`.  This is the graded Hilbert function of the section graded
module `M(X_s, F_s, L_s)` (`def:sectionGradedModule`); it uses only `H⁰`.
When the dimension is not finite, `Module.finrank` takes the junk value `0`.
Blueprint: the graded Hilbert function of `def:hilbert_polynomial`. -/
noncomputable def hilbertFunction (π : X ⟶ S) (L F : X.Modules) (s : S)
    (m : ℕ) : ℕ :=
  letI := π.fiberSectionsModule s
    (Scheme.Modules.moduleTensorPow (π.fiberModule s F) (π.fiberModule s L) m)
  Module.finrank (S.residueField s)
    Γ(Scheme.Modules.moduleTensorPow (π.fiberModule s F) (π.fiberModule s L) m, ⊤)

/-- Two rational polynomials that agree at all sufficiently large natural
arguments are equal: the agreement set is infinite, so the difference has
infinitely many roots. -/
private lemma eq_of_eval_nat_eventually_eq {Φ Ψ : Polynomial ℚ} {N₁ N₂ : ℕ}
    {f : ℕ → ℚ} (h₁ : ∀ m : ℕ, N₁ < m → Φ.eval (m : ℚ) = f m)
    (h₂ : ∀ m : ℕ, N₂ < m → Ψ.eval (m : ℚ) = f m) : Φ = Ψ := by
  refine Polynomial.eq_of_infinite_eval_eq _ _ ?_
  apply ((Set.Ioi_infinite (max N₁ N₂)).image
    (Nat.cast_injective (R := ℚ)).injOn).mono
  rintro x ⟨n, hn, rfl⟩
  rw [Set.mem_Ioi, sup_lt_iff] at hn
  exact Set.mem_setOf_eq ▸ (h₁ n hn.1).trans (h₂ n hn.2).symm

open Classical in
/-- The **Hilbert polynomial** of a sheaf of modules `F` on `X` over `S` at
the fibre over `s ∈ S`, relative to the line bundle `L`
(`def:hilbert_polynomial`, [Nitsure] §1; cf. [Hartshorne] III.5.2): the
unique polynomial `Φ_{F,s} ∈ ℚ[λ]` that agrees, for all `m ≫ 0`, with the
graded Hilbert function

`m ↦ dim_{κ(s)} Γ(X_s, F_s ⊗ L_s^{⊗m})`

of the fibre section module (`Scheme.hilbertFunction`), when such a
polynomial exists — and the junk value `0` otherwise.  Uniqueness holds
unconditionally (two polynomials agreeing at all large naturals are equal,
`Scheme.hilbertPolynomial_eq_of_eventually`), so the extraction is canonical.

For proper `X_s`, ample `L_s` and coherent `F_s` the existence condition
holds (graded Hilbert–Serre; the `IsRatHilb`-conditional form is
`Scheme.existsUnique_hilbertPolynomial_of_isRatHilb`, and the remaining input
is the finite generation `lem:sectionGradedModule_fg`), and for `m ≫ 0` the
graded Hilbert function agrees with the Euler characteristic
`χ(X_s, F_s ⊗ L_s^{⊗m})` by Serre vanishing, so `Φ_{F,s}` is the classical
(Snapper) Hilbert polynomial — no numerical invariant is lost.  When `F` is
`S`-flat the function `s ↦ Φ_{F,s}` is locally constant on `S`. -/
noncomputable def hilbertPolynomial [IsLocallyNoetherian S] (π : X ⟶ S)
    [LocallyOfFiniteType π] (L F : X.Modules) (s : S) :
    Polynomial ℚ :=
  if h : ∃ Φ : Polynomial ℚ, ∃ N : ℕ, ∀ m : ℕ, N < m →
      Φ.eval (m : ℚ) = (hilbertFunction π L F s m : ℚ)
  then h.choose else 0

section HilbertPolynomialApi

variable [IsLocallyNoetherian S] (π : X ⟶ S) [LocallyOfFiniteType π]
variable (L F : X.Modules) (s : S)

/-- **Well-definedness of the Hilbert polynomial**: any polynomial that agrees
with the graded Hilbert function `m ↦ dim_{κ(s)} Γ(X_s, F_s ⊗ L_s^{⊗m})` for
all `m ≫ 0` *is* `hilbertPolynomial π L F s`.  This is the uniqueness clause
of `def:hilbert_polynomial`. -/
theorem hilbertPolynomial_eq_of_eventually {Φ : Polynomial ℚ} {N : ℕ}
    (hΦ : ∀ m : ℕ, N < m → Φ.eval (m : ℚ) = (hilbertFunction π L F s m : ℚ)) :
    hilbertPolynomial π L F s = Φ := by
  have h : ∃ Φ' : Polynomial ℚ, ∃ N' : ℕ, ∀ m : ℕ, N' < m →
      Φ'.eval (m : ℚ) = (hilbertFunction π L F s m : ℚ) := ⟨Φ, N, hΦ⟩
  rw [hilbertPolynomial, dif_pos h]
  obtain ⟨N', hN'⟩ := h.choose_spec
  exact eq_of_eval_nat_eventually_eq hN' hΦ

/-- **Defining property of the Hilbert polynomial**: if some polynomial
agrees with the graded Hilbert function for all `m ≫ 0`, then
`hilbertPolynomial π L F s` does. -/
theorem hilbertPolynomial_eval_eventually
    (h : ∃ Φ : Polynomial ℚ, ∃ N : ℕ, ∀ m : ℕ, N < m →
      Φ.eval (m : ℚ) = (hilbertFunction π L F s m : ℚ)) :
    ∃ N : ℕ, ∀ m : ℕ, N < m →
      (hilbertPolynomial π L F s).eval (m : ℚ) = (hilbertFunction π L F s m : ℚ) := by
  obtain ⟨Φ, N, hΦ⟩ := h
  refine ⟨N, fun m hm => ?_⟩
  rw [hilbertPolynomial_eq_of_eventually π L F s hΦ]
  exact hΦ m hm

open PowerSeries in
omit [IsLocallyNoetherian S] [LocallyOfFiniteType π] in
/-- **Existence and uniqueness of the Hilbert polynomial from rationality of
the Hilbert series** (the polynomial-extraction step of
`thm:hilbertPoly_of_sectionModule`): if the graded Hilbert function of `F` at
`s` is a rational Hilbert function of some order `d`
(`AlgebraicGeometry.IsRatHilb`, the output of the graded Hilbert–Serre engine
`AlgebraicGeometry.gradedModule_hilbertSeries_rational`), then there is a
*unique* polynomial agreeing with it for all `m ≫ 0`.  Combines the
rationality datum with Mathlib's `Polynomial.existsUnique_hilbertPoly`
coefficient extraction (`lem:hilbertPoly_exists_mathlib`). -/
theorem existsUnique_hilbertPolynomial_of_isRatHilb {d : ℕ}
    (hrat : IsRatHilb (fun m => (hilbertFunction π L F s m : ℚ)) d) :
    ∃! Φ : Polynomial ℚ, ∃ N : ℕ, ∀ m : ℕ, N < m →
      Φ.eval (m : ℚ) = (hilbertFunction π L F s m : ℚ) := by
  obtain ⟨p, N, hp⟩ := hrat
  refine ⟨Polynomial.hilbertPoly p d, ⟨max N p.natDegree, fun m hm => ?_⟩, ?_⟩
  · rw [← Polynomial.coeff_mul_invOneSubPow_eq_hilbertPoly_eval d
      (lt_of_le_of_lt (le_max_right _ _) hm)]
    exact (hp m (lt_of_le_of_lt (le_max_left _ _) hm)).symm
  · rintro Ψ ⟨N', hΨ⟩
    refine eq_of_eval_nat_eventually_eq hΨ
      (f := fun m => (hilbertFunction π L F s m : ℚ)) (N₂ := max N p.natDegree)
      (fun m hm => ?_)
    rw [← Polynomial.coeff_mul_invOneSubPow_eq_hilbertPoly_eval d
      (lt_of_le_of_lt (le_max_right _ _) hm)]
    exact (hp m (lt_of_le_of_lt (le_max_left _ _) hm)).symm

open PowerSeries in
/-- Under the rationality hypothesis, `hilbertPolynomial π L F s` satisfies
the defining eventual-agreement property with the graded Hilbert function.
This is the conditional content of `thm:hilbertPoly_of_sectionModule`; the
geometric input producing `IsRatHilb` (properness of `X_s` + ampleness of
`L_s` via `lem:sectionGradedModule_fg`) is future work. -/
theorem hilbertPolynomial_eval_of_isRatHilb {d : ℕ}
    (hrat : IsRatHilb (fun m => (hilbertFunction π L F s m : ℚ)) d) :
    ∃ N : ℕ, ∀ m : ℕ, N < m →
      (hilbertPolynomial π L F s).eval (m : ℚ) = (hilbertFunction π L F s m : ℚ) :=
  hilbertPolynomial_eval_eventually π L F s
    (existsUnique_hilbertPolynomial_of_isRatHilb π L F s hrat).exists

open PowerSeries in
/-- The Hilbert polynomial computes as Mathlib's `Polynomial.hilbertPoly`
numerator-extraction applied to any rational-series presentation of the graded
Hilbert function. -/
theorem hilbertPolynomial_eq_hilbertPoly {p : Polynomial ℚ} {d N : ℕ}
    (hp : ∀ m : ℕ, N < m → (hilbertFunction π L F s m : ℚ) =
      ((p : ℚ⟦X⟧) * (PowerSeries.invOneSubPow ℚ d).val).coeff m) :
    hilbertPolynomial π L F s = Polynomial.hilbertPoly p d := by
  refine hilbertPolynomial_eq_of_eventually π L F s
    (N := max N p.natDegree) (fun m hm => ?_)
  rw [← Polynomial.coeff_mul_invOneSubPow_eq_hilbertPoly_eval d
    (lt_of_le_of_lt (le_max_right _ _) hm)]
  exact (hp m (lt_of_le_of_lt (le_max_left _ _) hm)).symm

end HilbertPolynomialApi

end Scheme

end AlgebraicGeometry
