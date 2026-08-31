/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.GradedHilbertSerre

/-!
# Finite-dimensional graded pieces of a finite polynomial module (D5)

The Serre D-phase abstract algebra lemma.  Let `κ` be a field and `M = ⨁ ℳ n` an
`ℕ`-graded `κ`-vector space.  A finite family `t : Fin r → End κ M` of pairwise
commuting endomorphisms, each raising degree by one (`RaisesDegree`), makes `M` a
module over `MvPolynomial (Fin r) κ` (`GradedModule.polyModule`, `X i` acting as
`t i`).  **If `M` is finitely generated over this polynomial ring, then every graded
piece `ℳ n` is finite-dimensional over `κ`.**

This is the finiteness input `[∀ n, FiniteDimensional κ (ℳ n)]` that the Stacks 00K1
Hilbert-series induction (`GradedModule.subquotient_hilbertSeries_rational`) assumes;
D5 discharges it from finite generation alone.

## Proof outline

* the action of a monomial `X^α` raises degree by `|α|`
  (`GradedModule.monomial_smul_mem`, by induction from `RaisesDegree` via
  `X_pow_smul_mem`);
* hence a homogeneous polynomial of degree `e` shifts degree by `e`
  (`GradedModule.homogeneous_smul_mem`);
* finite generators can be taken **homogeneous** (decompose each generator);
* the degree-`n` component of `p · h` (for a homogeneous generator `h ∈ ℳ d`) lies in
  the image of the *finite-dimensional* space
  `MvPolynomial.restrictTotalDegree (Fin r) κ n` under `· • h`
  (`GradedModule.decompose_smul_mem`); so `ℳ n` embeds in a finite supremum of
  finite-dimensional subspaces, hence is finite-dimensional.

Blueprint: `lem:graded_pieces_finite` (Serre D-phase).  Source: Stacks tag 00K1,
Atiyah–Macdonald Ch. 11.
-/

set_option autoImplicit false

open MvPolynomial DirectSum

namespace AlgebraicGeometry.GradedModule

variable {κ M : Type*} [Field κ] [AddCommGroup M] [Module κ M]
variable (ℳ : ℕ → Submodule κ M) [DirectSum.Decomposition ℳ]

section DegreeShift

omit [DirectSum.Decomposition ℳ]

variable {r : ℕ} (t : Fin r → Module.End κ M) (hcomm : ∀ i j, Commute (t i) (t j))
  (hraise : ∀ i, RaisesDegree ℳ (t i))

include hraise

/-- The action of a power `X i ^ k` raises degree by `k`. -/
lemma X_pow_smul_mem (i : Fin r) (k : ℕ) :
    ∀ (d : ℕ) (h : M), h ∈ ℳ d →
      letI := polyModule t hcomm
      ((X i : MvPolynomial (Fin r) κ) ^ k) • h ∈ ℳ (d + k) := by
  letI := polyModule t hcomm
  induction k with
  | zero => intro d h hh; simpa using hh
  | succ k ih =>
      intro d h hh
      rw [pow_succ, mul_smul, polyModule_X_smul]
      have key := ih (d + 1) (t i h) ((hraise i).mem ℳ hh)
      have hde : d + 1 + k = d + (k + 1) := by omega
      rwa [hde] at key

/-- The action of a monomial `X^α` raises degree by the total degree `|α|`. -/
lemma monomial_smul_mem (α : Fin r →₀ ℕ) :
    ∀ (d : ℕ) (h : M), h ∈ ℳ d →
      letI := polyModule t hcomm
      (monomial α (1 : κ)) • h ∈ ℳ (d + α.degree) := by
  letI := polyModule t hcomm
  induction α using Finsupp.induction with
  | zero => intro d h hh; simpa using hh
  | single_add a b f haf hb ih =>
      intro d h hh
      have hsplit : (monomial (Finsupp.single a b + f) (1 : κ) : MvPolynomial (Fin r) κ)
          = (X a ^ b) * monomial f 1 := by
        rw [X_pow_eq_monomial, monomial_mul, one_mul]
      rw [hsplit, mul_smul]
      have key := X_pow_smul_mem ℳ t hcomm hraise a b (d + f.degree)
        (monomial f 1 • h) (ih d h hh)
      have hde : d + f.degree + b = d + (Finsupp.single a b + f).degree := by
        rw [map_add, Finsupp.degree_single]; omega
      rwa [hde] at key

/-- The action of a homogeneous polynomial of degree `e` shifts degree by `e`. -/
lemma homogeneous_smul_mem {e : ℕ} {q : MvPolynomial (Fin r) κ} (hq : q.IsHomogeneous e)
    (d : ℕ) (h : M) (hh : h ∈ ℳ d) :
    letI := polyModule t hcomm
    q • h ∈ ℳ (d + e) := by
  letI := polyModule t hcomm
  haveI := polyModule_isScalarTower t hcomm
  rw [q.as_sum, Finset.sum_smul]
  refine Submodule.sum_mem _ fun v hv => ?_
  have hvdeg : v.degree = e := by
    rw [Finsupp.degree_eq_weight_one]; exact hq (mem_support_iff.mp hv)
  have hmono : (monomial v (coeff v q) : MvPolynomial (Fin r) κ)
      = (coeff v q) • monomial v 1 := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hmono, smul_assoc]
  refine Submodule.smul_mem _ _ ?_
  have := monomial_smul_mem ℳ t hcomm hraise v d h hh
  rwa [hvdeg] at this

end DegreeShift

section Projection

variable {r : ℕ} (t : Fin r → Module.End κ M) (hcomm : ∀ i j, Commute (t i) (t j))
  (hraise : ∀ i, RaisesDegree ℳ (t i))

include hraise

/-- The degree-`n` component of `p · h`, for a homogeneous `h ∈ ℳ d`, lies in the image of the
finite-dimensional space `restrictTotalDegree (Fin r) κ n` under `· • h`: expand `p` into its
homogeneous components, whose degree-`e` part contributes only to degree `d + e`, so the degree-`n`
survivor is `(homogeneousComponent (n - d) p) • h` with `homogeneousComponent (n-d) p` of total
degree `≤ n`. -/
lemma decompose_smul_mem (n : ℕ) (p : MvPolynomial (Fin r) κ) (d : ℕ) (h : M) (hh : h ∈ ℳ d) :
    letI := polyModule t hcomm
    letI := polyModule_isScalarTower t hcomm
    (DirectSum.decompose ℳ (p • h) n : M) ∈
      (MvPolynomial.restrictTotalDegree (Fin r) κ n).map
        ((LinearMap.toSpanSingleton (MvPolynomial (Fin r) κ) M h).restrictScalars κ) := by
  classical
  letI := polyModule t hcomm
  letI := polyModule_isScalarTower t hcomm
  set φ := (LinearMap.toSpanSingleton (MvPolynomial (Fin r) κ) M h).restrictScalars κ with hφ
  have hpsum : p • h = ∑ e ∈ Finset.range (p.totalDegree + 1),
      (MvPolynomial.homogeneousComponent e p) • h := by
    rw [← Finset.sum_smul, MvPolynomial.sum_homogeneousComponent]
  have hsum : (DirectSum.decompose ℳ (p • h) n : M)
      = ∑ e ∈ Finset.range (p.totalDegree + 1),
          (DirectSum.decompose ℳ ((MvPolynomial.homogeneousComponent e p) • h) n : M) := by
    rw [hpsum, DirectSum.decompose_sum, DirectSum.sum_apply, AddSubmonoidClass.coe_finsetSum]
  rw [hsum]
  refine Submodule.sum_mem _ fun e _ => ?_
  have hye : (MvPolynomial.homogeneousComponent e p : MvPolynomial (Fin r) κ) • h ∈ ℳ (d + e) :=
    homogeneous_smul_mem ℳ t hcomm hraise
      (MvPolynomial.homogeneousComponent_isHomogeneous e p) d h hh
  by_cases hn : d + e = n
  · have heq : (DirectSum.decompose ℳ ((MvPolynomial.homogeneousComponent e p) • h) n : M)
        = (MvPolynomial.homogeneousComponent e p) • h := by
      rw [← hn]; exact DirectSum.decompose_of_mem_same ℳ hye
    rw [heq]
    have hmem : (MvPolynomial.homogeneousComponent e p : MvPolynomial (Fin r) κ)
        ∈ MvPolynomial.restrictTotalDegree (Fin r) κ n := by
      rw [MvPolynomial.mem_restrictTotalDegree]
      exact le_trans (MvPolynomial.homogeneousComponent_isHomogeneous e p).totalDegree_le (by omega)
    have hap : (MvPolynomial.homogeneousComponent e p : MvPolynomial (Fin r) κ) • h
        = φ (MvPolynomial.homogeneousComponent e p) := by
      rw [hφ, LinearMap.restrictScalars_apply, LinearMap.toSpanSingleton_apply]
    rw [hap]
    exact Submodule.mem_map_of_mem hmem
  · rw [DirectSum.decompose_of_mem_ne ℳ hye hn]
    exact Submodule.zero_mem _

/-- **Finite-dimensional graded pieces (D5).**  If the ℕ-graded `κ`-vector space `M = ⨁ ℳ n`
is *finitely generated* over `MvPolynomial (Fin r) κ` acting through the degree-raising family
`t` (`polyModule`), then every graded piece `ℳ n` is finite-dimensional over `κ`.

Take finite generators; their homogeneous components `{h ∈ ℳ e}` are finitely many and generate.
For `x ∈ ℳ n`, writing `x = ∑ p_g · g` and projecting to degree `n`, each contribution
`(decompose (p_g · h) n)` lands in the image of the *finite-dimensional* space
`restrictTotalDegree (Fin r) κ n` under `· • h` (`decompose_smul_mem`).  Thus `ℳ n` embeds in a
finite supremum of finite-dimensional subspaces. -/
theorem finiteDimensional_of_polyModule_finite
    (hfin : letI := polyModule t hcomm; Module.Finite (MvPolynomial (Fin r) κ) M) (n : ℕ) :
    FiniteDimensional κ (ℳ n) := by
  classical
  letI := polyModule t hcomm
  letI := polyModule_isScalarTower t hcomm
  obtain ⟨s, hs⟩ := hfin.fg_top
  -- the finite set of (homogeneous component, its degree) over all generators
  set P : Finset (M × ℕ) := s.biUnion fun g =>
    (DirectSum.decompose ℳ g).support.image fun e => ((DirectSum.decompose ℳ g e : M), e) with hP
  -- the finite supremum of finite-dimensional images
  set N : Submodule κ M := ⨆ q ∈ P, (MvPolynomial.restrictTotalDegree (Fin r) κ n).map
    ((LinearMap.toSpanSingleton (MvPolynomial (Fin r) κ) M q.1).restrictScalars κ) with hN
  haveI hNfd : FiniteDimensional κ N := by
    refine Module.Finite.iff_fg.mpr ?_
    rw [hN]
    refine Submodule.fg_biSup P _ fun q _ => ?_
    exact Submodule.FG.map _ (Module.Finite.iff_fg.mp inferInstance)
  refine Submodule.finiteDimensional_of_le (S₂ := N) fun x hx => ?_
  -- represent `x` through the generators
  have hxtop : x ∈ Submodule.span (MvPolynomial (Fin r) κ) (↑s : Set M) := by
    rw [hs]; exact Submodule.mem_top
  obtain ⟨c, _, hc⟩ := Submodule.mem_span_finset.mp hxtop
  rw [(DirectSum.decompose_of_mem_same ℳ hx).symm, ← hc]
  have hstep : (DirectSum.decompose ℳ (∑ g ∈ s, c g • g) n : M)
      = ∑ g ∈ s, (DirectSum.decompose ℳ (c g • g) n : M) := by
    rw [DirectSum.decompose_sum, DirectSum.sum_apply, AddSubmonoidClass.coe_finsetSum]
  rw [hstep]
  refine Submodule.sum_mem _ fun g hg => ?_
  -- expand each (non-homogeneous) generator into its homogeneous components
  have hcg : c g • g = ∑ e ∈ (DirectSum.decompose ℳ g).support,
      c g • (DirectSum.decompose ℳ g e : M) := by
    conv_rhs => rw [← Finset.smul_sum, DirectSum.sum_support_decompose ℳ g]
  have hgstep : (DirectSum.decompose ℳ (c g • g) n : M)
      = ∑ e ∈ (DirectSum.decompose ℳ g).support,
          (DirectSum.decompose ℳ (c g • (DirectSum.decompose ℳ g e : M)) n : M) := by
    rw [hcg, DirectSum.decompose_sum, DirectSum.sum_apply, AddSubmonoidClass.coe_finsetSum]
  rw [hgstep]
  refine Submodule.sum_mem _ fun e he => ?_
  have hmemP : ((DirectSum.decompose ℳ g e : M), e) ∈ P := by
    rw [hP]; exact Finset.mem_biUnion.mpr ⟨g, hg, Finset.mem_image.mpr ⟨e, he, rfl⟩⟩
  have hce := decompose_smul_mem ℳ t hcomm hraise n (c g) e
    (DirectSum.decompose ℳ g e) (SetLike.coe_mem _)
  have hsub : (MvPolynomial.restrictTotalDegree (Fin r) κ n).map
      ((LinearMap.toSpanSingleton (MvPolynomial (Fin r) κ) M
        (DirectSum.decompose ℳ g e : M)).restrictScalars κ) ≤ N := by
    rw [hN]
    exact le_iSup₂_of_le ((DirectSum.decompose ℳ g e : M), e) hmemP le_rfl
  exact hsub hce

end Projection

end AlgebraicGeometry.GradedModule
