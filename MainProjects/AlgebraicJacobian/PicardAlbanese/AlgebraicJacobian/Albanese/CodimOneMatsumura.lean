/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import AlgebraicJacobian.Algebra.ABRegularCM

/-!
# Matsumura's regular-sequence criterion (Thm 14.2 / Stacks 00NQ)

Ported from §3.C of `Albanese/CodimOneExtension.lean` of the previous
Algebraic-Jacobian tree (identical toolchain and mathlib pin),
re-kernel-verified here.

Headline: `matsumura_isRegular_of_linearIndependent_cotangent` — on a regular
local Noetherian ring `(A, 𝔪)`, a finite sequence `f₁, …, f_c ∈ 𝔪` whose
images in the cotangent space `𝔪/𝔪²` are `κ(A)`-linearly independent forms a
`RingTheory.Sequence.IsRegular` sequence (Matsumura, *Commutative Ring
Theory*, Thm 14.2; Stacks tag `00NQ`).

The induction peels the head `f₁` via the ring-quotient cons rule
(`isRegular_cons_of_quotient_ring`, transporting Mathlib's `QuotSMulTop`-
flavoured `IsRegular.cons'` across `quotSMulTop_quotientRing_linearEquiv`);
the head is a non-zero-divisor since `A` is a domain
(`RingTheory.CohenMacaulay.isDomain_of_regularLocal`), the quotient
`A ⧸ span{f₁}` is again regular local
(`RingTheory.CohenMacaulay.regularLocal_quotient_isRegularLocal_of_notMemSq`),
and the tail's cotangent classes stay independent in the quotient
(`matsumura_descent_cotangent`).

Project-local because Mathlib at this pin ships neither the criterion nor the
regular-local ⟹ domain / regular-local-quotient facts it consumes (both come
from the `Algebra/ABRegular*` Auslander–Buchsbaum package). Not consumed by
the current extension chain (the regularity route runs Serre-free through
`Algebra/SmoothPrimeRegularity.lean`); retained as reusable regular-sequence
infrastructure for the Milne-3.3 lane and beyond.

Porting note: the source's `set_option maxHeartbeats 1600000 in` on
`matsumura_descent_cotangent` (an *elaboration* budget for the cotangent-map
kernel computation, not a kernel-timeout workaround) is carried unchanged.
-/

set_option autoImplicit false

universe u

/-! ## §3.C. Project-local Mathlib supplement — Matsumura regular-sequence bridge
(iter-203, Step A1)

Lane COE Step A1 substrate (Matsumura *Commutative Ring Theory* Thm 14.2 /
Stacks 00NQ). The goal of this section is the criterion: on a regular local
Noetherian ring `(A, 𝔪)`, a finite sequence `f₁,…,f_c ∈ 𝔪` whose images in the
cotangent space `𝔪/𝔪²` are `κ`-linearly independent forms a
`RingTheory.Sequence.IsRegular` sequence.

The induction is on the length `c`, peeling the head `f₁`. The mathematical
peeling step uses `RingTheory.Sequence.IsRegular.cons'`, whose tail lives over
the *module* quotient `QuotSMulTop f₁ A = A ⧸ (f₁ • ⊤)`. The two bridges below
convert that module-quotient bookkeeping into the *ring* quotient
`A ⧸ Ideal.span {f₁}` (over which the induction hypothesis is naturally
phrased): `quotSMulTop_quotientRing_linearEquiv` is the canonical
`(A ⧸ span{f₁})`-linear identification `QuotSMulTop f₁ A ≃ₗ A ⧸ span{f₁}`, and
`isRegular_cons_of_quotient_ring` is the resulting clean cons rule.

These are project-local because Mathlib ships only the `QuotSMulTop`-flavoured
`IsRegular.cons'`; the ring-quotient repackaging is what makes a downstream
ring-theoretic induction (the Matsumura criterion) ergonomic. -/

/-- **Step A1 bridge (iter-203).** The canonical `(A ⧸ span{r})`-linear
equivalence between the module quotient `QuotSMulTop r A = A ⧸ (r • ⊤)` and the
ring quotient `A ⧸ span{r}`. Built by composing Mathlib's
`QuotSMulTop.equivQuotTensor` (`QuotSMulTop r A ≃ₗ[A] (A⧸span{r}) ⊗[A] A`) with
`TensorProduct.rid` and then promoting the resulting `A`-linear equivalence to
an `(A⧸span{r})`-linear one via `LinearEquiv.extendScalarsOfSurjective` along the
surjective quotient map. Axiom-clean. -/
private noncomputable def quotSMulTop_quotientRing_linearEquiv
    {A : Type u} [CommRing A] (r : A) :
    QuotSMulTop r A ≃ₗ[A ⧸ Ideal.span {r}] (A ⧸ Ideal.span {r}) :=
  LinearEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
    ((QuotSMulTop.equivQuotTensor r A) ≪≫ₗ (TensorProduct.rid A (A ⧸ Ideal.span {r})))

/-- **Step A1 bridge (iter-203).** Ring-quotient cons rule for regular
sequences: given `IsSMulRegular A r` and a regular sequence over the ring
quotient `A ⧸ span{r}` on the images of `rs`, the list `r :: rs` is a regular
sequence over `A`. This is the ergonomic ring-quotient form of Mathlib's
`RingTheory.Sequence.IsRegular.cons'` (whose tail lives over the module quotient
`QuotSMulTop r A`), transported across `quotSMulTop_quotientRing_linearEquiv` via
`LinearEquiv.isRegular_congr`. Axiom-clean. -/
private theorem isRegular_cons_of_quotient_ring
    {A : Type u} [CommRing A] {r : A} {rs : List A}
    (h1 : IsSMulRegular A r)
    (h2 : RingTheory.Sequence.IsRegular (A ⧸ Ideal.span {r})
            (rs.map (Ideal.Quotient.mk (Ideal.span {r})))) :
    RingTheory.Sequence.IsRegular A (r :: rs) := by
  apply RingTheory.Sequence.IsRegular.cons' h1
  exact ((quotSMulTop_quotientRing_linearEquiv r).symm.isRegular_congr _).mp h2

set_option maxHeartbeats 1600000 in
-- The cotangent-map kernel computation + the hand-rolled `linearIndependent_iff`
-- argument are heartbeat-heavy; the default budget is insufficient.
/-- **Step A1 cotangent linear-independence descent (iter-203).** The inductive
descent step of the Matsumura criterion: if the cotangent classes of a sequence
`f₀, f₁, …, f_m ∈ 𝔪` are `κ(A)`-linearly independent, then the cotangent classes
of the *tail* `f₁, …, f_m`, pushed into the quotient `A' = A ⧸ span{f₀}`, are
`κ(A')`-linearly independent in `𝔪'/𝔪'²`.

This is the genuine mathematical content of the descent (the part the iter-203
blueprint recipe flagged as a `LinearIndependent.map`/`.image` step). The proof
constructs the `A`-linear cotangent map `π : 𝔪.Cotangent →ₗ[A] 𝔪'.Cotangent`
(Mathlib's `Ideal.mapCotangent` for the quotient algebra `A → A'`), shows it is
surjective with kernel `A ∙ (𝔪.toCotangent f₀)` (via
`Ideal.mapCotangent_ker_of_surjective`, using `span{f₀} ⊓ 𝔪 = span{f₀}`), and
then runs the kernel-disjointness/linear-independence argument by hand through
`Fintype.linearIndependent_iff`: a `κ(A')`-relation on the tail images lifts to
an `A`-relation `∑ aᵢ • π(vᵢ₊₁) = 0`, hence `∑ aᵢ • vᵢ₊₁ ∈ ker π = A ∙ v₀`, so
reducing modulo `𝔪` and applying the full `κ(A)`-independence forces every
`residue (aᵢ) = 0`, whence every original `κ(A')`-coefficient vanishes (the
residue fields are matched through `algebraMap A A'`, no explicit residue-field
isomorphism is needed).

Project-local because Mathlib ships `Ideal.mapCotangent` and its kernel/surjectivity
lemmas but not this regular-local descent packaging. Axiom-clean. -/
private theorem matsumura_descent_cotangent
    {A : Type u} [CommRing A] [IsLocalRing A]
    (m : ℕ) (rs : Fin (m + 1) → A) (hmem : ∀ i, rs i ∈ IsLocalRing.maximalIdeal A)
    [IsLocalRing (A ⧸ Ideal.span ({rs 0} : Set A))]
    (hlin : LinearIndependent (IsLocalRing.ResidueField A)
       (fun i => (IsLocalRing.maximalIdeal A).toCotangent ⟨rs i, hmem i⟩))
    (hg'mem : ∀ i : Fin m, (Ideal.Quotient.mk (Ideal.span ({rs 0} : Set A)) (rs i.succ))
       ∈ IsLocalRing.maximalIdeal (A ⧸ Ideal.span ({rs 0} : Set A))) :
    LinearIndependent (IsLocalRing.ResidueField (A ⧸ Ideal.span ({rs 0} : Set A)))
      (fun i : Fin m => (IsLocalRing.maximalIdeal (A ⧸ Ideal.span ({rs 0} : Set A))).toCotangent
        ⟨Ideal.Quotient.mk (Ideal.span ({rs 0} : Set A)) (rs i.succ), hg'mem i⟩) := by
  set x := rs 0 with hxdef
  have hxmem : x ∈ IsLocalRing.maximalIdeal A := hmem 0
  set B := A ⧸ Ideal.span ({x} : Set A) with hB
  have hsurj : Function.Surjective (algebraMap A B) := Ideal.Quotient.mk_surjective
  have halg : algebraMap A B = Ideal.Quotient.mk (Ideal.span ({x} : Set A)) :=
    Ideal.Quotient.algebraMap_eq _
  have hkerm : RingHom.ker (algebraMap A B) = Ideal.span ({x} : Set A) := by
    rw [halg]; exact Ideal.mk_ker
  have hcomap : Ideal.comap (algebraMap A B) (IsLocalRing.maximalIdeal B)
      = IsLocalRing.maximalIdeal A :=
    (IsLocalRing.isMaximal_iff A).mp (Ideal.comap_isMaximal_of_surjective _ hsurj)
  have heq : Ideal.comap (algebraMap A B) (IsLocalRing.maximalIdeal B)
      = RingHom.ker (algebraMap A B) ⊔ IsLocalRing.maximalIdeal A := by
    rw [hcomap, hkerm, sup_eq_right.mpr]; rwa [Ideal.span_le, Set.singleton_subset_iff]
  have hle : IsLocalRing.maximalIdeal A
      ≤ Ideal.comap (Algebra.ofId A B) (IsLocalRing.maximalIdeal B) := hcomap.ge
  set π := (IsLocalRing.maximalIdeal A).mapCotangent (IsLocalRing.maximalIdeal B)
    (Algebra.ofId A B) hle with hπdef
  have hπker := Ideal.mapCotangent_ker_of_surjective
    (I := IsLocalRing.maximalIdeal B) (J := IsLocalRing.maximalIdeal A) hsurj heq
  have hxsq : Ideal.span ({x} : Set A) ⊓ IsLocalRing.maximalIdeal A = Ideal.span ({x} : Set A) := by
    rw [inf_eq_left, Ideal.span_le, Set.singleton_subset_iff]; exact hxmem
  have hcomapsub : Submodule.comap (Submodule.subtype (IsLocalRing.maximalIdeal A))
      (Ideal.span ({x} : Set A))
      = Submodule.span A {(⟨x, hxmem⟩ : IsLocalRing.maximalIdeal A)} := by
    apply le_antisymm
    · rintro ⟨a, ha⟩ hain
      simp only [Submodule.mem_comap, Submodule.coe_subtype] at hain
      rw [Ideal.mem_span_singleton'] at hain
      obtain ⟨r, rfl⟩ := hain
      rw [Submodule.mem_span_singleton]; exact ⟨r, by ext; simp⟩
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      simp only [SetLike.mem_coe, Submodule.mem_comap, Submodule.coe_subtype]
      exact Ideal.mem_span_singleton_self x
  have hkerπ : LinearMap.ker π
      = Submodule.span A {(IsLocalRing.maximalIdeal A).toCotangent ⟨x, hxmem⟩} := by
    rw [hπdef, hπker, hkerm, hxsq, hcomapsub, Submodule.map_span]; congr 1; simp
  set v : Fin (m + 1) → IsLocalRing.CotangentSpace A :=
    fun i => (IsLocalRing.maximalIdeal A).toCotangent ⟨rs i, hmem i⟩ with hvdef
  have hF1 : ∀ i : Fin m, π (v i.succ) = (IsLocalRing.maximalIdeal B).toCotangent
      ⟨Ideal.Quotient.mk (Ideal.span ({x} : Set A)) (rs i.succ), hg'mem i⟩ := by
    intro i; rw [hvdef, hπdef, Ideal.mapCotangent_toCotangent]; congr 1
  rw [show (fun i : Fin m => (IsLocalRing.maximalIdeal B).toCotangent
      ⟨Ideal.Quotient.mk (Ideal.span ({x} : Set A)) (rs i.succ), hg'mem i⟩)
      = (fun i => π (v i.succ)) from by funext i; rw [hF1]]
  have e1 : ∀ (r : A) (y : IsLocalRing.CotangentSpace A),
      r • y = (IsLocalRing.residue A r) • y := fun r y => by
    rw [← IsScalarTower.algebraMap_smul (IsLocalRing.ResidueField A) r y]; rfl
  have e1B : ∀ (r : B) (y : IsLocalRing.CotangentSpace B),
      r • y = (IsLocalRing.residue B r) • y := fun r y => by
    rw [← IsScalarTower.algebraMap_smul (IsLocalRing.ResidueField B) r y]; rfl
  have hρsurj : Function.Surjective (fun a : A => IsLocalRing.residue B (algebraMap A B a)) :=
    (IsLocalRing.residue_surjective).comp hsurj
  rw [Fintype.linearIndependent_iff]
  intro g hg
  choose a ha using fun i => hρsurj (g i)
  have hai : ∀ i, IsLocalRing.residue B (algebraMap A B (a i)) = g i := ha
  have hstep : ∀ i : Fin m, g i • π (v i.succ) = a i • π (v i.succ) := by
    intro i
    rw [← hai i, ← e1B (algebraMap A B (a i)) (π (v i.succ)),
        IsScalarTower.algebraMap_smul B (a i) (π (v i.succ))]
  have hsumeq : ∑ i, g i • π (v i.succ) = π (∑ i, a i • v i.succ) := by
    rw [map_sum]; exact Finset.sum_congr rfl (fun i _ => by rw [hstep i, map_smul])
  rw [hsumeq] at hg
  have hmemker : (∑ i, a i • v i.succ) ∈ LinearMap.ker π := hg
  rw [hkerπ, Submodule.mem_span_singleton] at hmemker
  obtain ⟨b, hb⟩ := hmemker
  have hκ : (IsLocalRing.residue A b) • v 0 = ∑ i, (IsLocalRing.residue A (a i)) • v i.succ := by
    rw [← e1 b (v 0), hb]; exact Finset.sum_congr rfl (fun i _ => e1 (a i) (v i.succ))
  have hzero : ∑ j, (Fin.cons (IsLocalRing.residue A b) (fun i => -(IsLocalRing.residue A (a i))) :
      Fin (m + 1) → IsLocalRing.ResidueField A) j • v j = 0 := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, neg_smul]
    rw [hκ, ← Finset.sum_add_distrib]; simp
  have hall := Fintype.linearIndependent_iff.mp hlin _ hzero
  intro i
  have hd : IsLocalRing.residue A (a i) = 0 := by
    have h := hall i.succ; rw [Fin.cons_succ] at h; exact neg_eq_zero.mp h
  have hai_mem : a i ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.residue_eq_zero_iff (a i)).mp hd
  rw [← hai i]
  change IsLocalRing.residue B (algebraMap A B (a i)) = 0
  rw [IsLocalRing.residue_eq_zero_iff]
  have hcm : a i ∈ Ideal.comap (algebraMap A B) (IsLocalRing.maximalIdeal B) := by
    rw [hcomap]; exact hai_mem
  exact Ideal.mem_comap.mp hcm

/-- **Step A1 — Matsumura's regular-sequence criterion (iter-203, Lane COE).**
On a regular local Noetherian ring `(A, 𝔪)`, a finite sequence `f₁, …, f_c ∈ 𝔪`
whose images in the cotangent space `𝔪/𝔪²` are `κ(A)`-linearly independent forms
a `RingTheory.Sequence.IsRegular` sequence.

This is Matsumura, *Commutative Ring Theory*, Thm 14.2 (cf. Stacks tag `00NQ`):
linearly independent elements of `𝔪/𝔪²` in a regular local ring form a regular
sequence (indeed they extend to a regular system of parameters). The proof is
the iter-203 blueprint recipe `\subsec:stage6_iib_substrate_iter200`, Step A1:
induction on the length `c` (here `n`), peeling the head `f₁` via
`isRegular_cons_of_quotient_ring`. At each step the head is a non-zero-divisor
(`A` is a domain by `RingTheory.CohenMacaulay.isDomain_of_regularLocal`, and
`f₁ ≠ 0` since `f₁ ∉ 𝔪²`), the quotient `A ⧸ span{f₁}` is again regular local
(`RingTheory.CohenMacaulay.regularLocal_quotient_isRegularLocal_of_notMemSq`),
and the tail's cotangent classes stay `κ`-linearly independent in the quotient
(`matsumura_descent_cotangent`). The two
`RingTheory.CohenMacaulay.*` inputs were promoted to public in iter-202.

Project-local because Mathlib at commit `b80f227` ships neither this criterion
nor the regular-local⟹domain / regular-local-quotient facts it consumes.
Axiom-clean. -/
theorem matsumura_isRegular_of_linearIndependent_cotangent
    {A : Type u} [CommRing A] [IsRegularLocalRing A]
    (n : ℕ) (rs : Fin n → A) (hrs_mem : ∀ i, rs i ∈ IsLocalRing.maximalIdeal A)
    (h_lin : LinearIndependent (IsLocalRing.ResidueField A)
               (fun i => (IsLocalRing.maximalIdeal A).toCotangent ⟨rs i, hrs_mem i⟩)) :
    RingTheory.Sequence.IsRegular A (List.ofFn rs) := by
  suffices H : ∀ (n : ℕ) (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      [IsRegularLocalRing A] (rs : Fin n → A)
      (hrs_mem : ∀ i, rs i ∈ IsLocalRing.maximalIdeal A),
      LinearIndependent (IsLocalRing.ResidueField A)
        (fun i => (IsLocalRing.maximalIdeal A).toCotangent ⟨rs i, hrs_mem i⟩) →
      RingTheory.Sequence.IsRegular A (List.ofFn rs) from H n A rs hrs_mem h_lin
  clear h_lin hrs_mem rs n
  intro n
  induction n with
  | zero =>
    intro A _ _ _ _ rs _ _
    rw [List.ofFn_zero]; exact RingTheory.Sequence.IsRegular.nil A A
  | succ m ih =>
    intro A _ _ _ _ rs hmem hlin
    have hxmem : rs 0 ∈ IsLocalRing.maximalIdeal A := hmem 0
    have hxne0 : (IsLocalRing.maximalIdeal A).toCotangent ⟨rs 0, hxmem⟩ ≠ 0 := hlin.ne_zero 0
    have hxnotsq : rs 0 ∉ IsLocalRing.maximalIdeal A ^ 2 := fun hsq =>
      hxne0 ((Ideal.toCotangent_eq_zero _ ⟨rs 0, hxmem⟩).mpr hsq)
    have hspan_pos : ∃ k, (IsLocalRing.maximalIdeal A).spanFinrank = k + 1 := by
      rcases Nat.eq_zero_or_pos ((IsLocalRing.maximalIdeal A).spanFinrank) with h0 | hpos
      · exfalso
        have hfg : (IsLocalRing.maximalIdeal A).FG := Ideal.fg_of_isNoetherianRing _
        have hbot : IsLocalRing.maximalIdeal A = ⊥ :=
          (Submodule.spanFinrank_eq_zero_iff_eq_bot hfg).mp h0
        apply hxnotsq
        have hb : rs 0 ∈ (⊥ : Ideal A) := hbot ▸ hxmem
        rw [Submodule.mem_bot] at hb; rw [hb]; exact Ideal.zero_mem _
      · exact ⟨(IsLocalRing.maximalIdeal A).spanFinrank - 1, by omega⟩
    obtain ⟨k, hk⟩ := hspan_pos
    obtain ⟨hNT, hLR, hRLR, _hdim_quot⟩ :=
      RingTheory.CohenMacaulay.regularLocal_quotient_isRegularLocal_of_notMemSq
        hk (rs 0) hxmem hxnotsq
    haveI : Nontrivial (A ⧸ Ideal.span ({rs 0} : Set A)) := hNT
    haveI : IsLocalRing (A ⧸ Ideal.span ({rs 0} : Set A)) := hLR
    haveI : IsRegularLocalRing (A ⧸ Ideal.span ({rs 0} : Set A)) := hRLR
    haveI : IsNoetherianRing (A ⧸ Ideal.span ({rs 0} : Set A)) := inferInstance
    have hg_mem : ∀ i : Fin m, (Ideal.Quotient.mk (Ideal.span ({rs 0} : Set A)) (rs i.succ))
        ∈ IsLocalRing.maximalIdeal (A ⧸ Ideal.span ({rs 0} : Set A)) := by
      intro i
      have hmax : (Ideal.comap (Ideal.Quotient.mk (Ideal.span ({rs 0} : Set A)))
          (IsLocalRing.maximalIdeal (A ⧸ Ideal.span ({rs 0} : Set A)))).IsMaximal :=
        Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
      have hc : Ideal.comap (Ideal.Quotient.mk (Ideal.span ({rs 0} : Set A)))
          (IsLocalRing.maximalIdeal (A ⧸ Ideal.span ({rs 0} : Set A)))
          = IsLocalRing.maximalIdeal A := (IsLocalRing.isMaximal_iff A).mp hmax
      have hin : rs i.succ ∈ Ideal.comap (Ideal.Quotient.mk (Ideal.span ({rs 0} : Set A)))
          (IsLocalRing.maximalIdeal (A ⧸ Ideal.span ({rs 0} : Set A))) := by
        rw [hc]; exact hmem i.succ
      exact Ideal.mem_comap.mp hin
    have hlin' := matsumura_descent_cotangent m rs hmem hlin hg_mem
    have hih := ih (A ⧸ Ideal.span ({rs 0} : Set A))
      (fun i => Ideal.Quotient.mk (Ideal.span ({rs 0} : Set A)) (rs i.succ)) hg_mem hlin'
    haveI : IsDomain A := RingTheory.CohenMacaulay.isDomain_of_regularLocal A
    have hxne0' : rs 0 ≠ 0 := fun h => hxnotsq (by rw [h]; exact Ideal.zero_mem _)
    have h1 : IsSMulRegular A (rs 0) := IsSMulRegular.of_ne_zero hxne0'
    rw [List.ofFn_succ]
    apply isRegular_cons_of_quotient_ring h1
    have hmapeq : (List.ofFn (fun i : Fin m => rs i.succ)).map
        (Ideal.Quotient.mk (Ideal.span ({rs 0} : Set A)))
        = List.ofFn (fun i => Ideal.Quotient.mk (Ideal.span ({rs 0} : Set A)) (rs i.succ)) := by
      rw [List.map_ofFn]; rfl
    rw [hmapeq]; exact hih
