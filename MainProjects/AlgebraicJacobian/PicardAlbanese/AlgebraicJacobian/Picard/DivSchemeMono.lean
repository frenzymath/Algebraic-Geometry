/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorStalkIdeal
import AlgebraicJacobian.Picard.DivisorFamilyEpsMono

/-!
# DDR-8 — the relative mono / Law-1 core (`informal/spec-dd-r.md` §3 item 7)

The **relative mono**: two certified divisor families over the test ring `R` whose
embedding pairs `ε` agree are equal in `DivFam` (i.e. cut the same divisor, `DivEq`).
This is the relative-level upgrade of DD-4 Task 6's field-level mono
(`AlgebraicGeometry.eq_of_divFamEps_eq`, I-0214) and is the Law-1 input DDR-9 consumes
(`informal/spec-dd-r.md` §3 item 8; Addendum 1, restated against `DivFamZar` — DDR-8 is
per-certified-representative, hence unaffected, and feeds the restated DDR-9 unchanged).

## The route (spec §3 item 7)

`DivEq d₁ d₂` (`Scheme.LocalEquations.DivEq`) asks, on a common refinement of the two
covers, for the local equations to differ by a **unit** at every point — a *relative*
unit over `R`, not merely a fibrewise one.  The spec route is: fibrewise both families
present the base divisor `bd(K_M ⊗ κ(p))` (DDR-2's certified-degree pinch +
`baseDivisorAt_window_normalization`), so at each residue field the two equations have
equal `ordZ` at every closed point (`coeffAt_eq_toAdd_ordZ_eqn`), i.e. their ratio is a
fibrewise unit; the colon-Tor pair upgrades fibrewise divisibility both ways to relative
divisibility, and residue-nonvanishing turns "each divides the other" into a relative
unit — hence `DivEq`.

This file lands the **argument assembled on those inputs**, in two layers.

* **§1 — the general upgrade** `Scheme.LocalEquations.divEq_of_stalkIdeal_eq`
  (fully proven, base-free): if two local-equation systems have the **same stalk ideal at
  every point** then they are `DivEq`.  This is the honest scheme-level form of
  "divisibility both ways + residue-nonvanishing ⟹ relative unit ⟹ `DivEq`": on the
  common refinement each equation lies germwise in the span of the other
  (`germ_eqn_span_eq` + the pointwise stalk-ideal equality), so by stalk-locality of
  regular principal ideals (`Scheme.mem_span_singleton_of_forall_germ`, DD-4 substrate)
  each divides the other *over the whole piece*; regularity of the equations
  (nonzerodivisors) turns the two cofactors into mutual inverses, i.e. a genuine unit.
  It is the exact converse of the landed `stalkIdeal_eq_of_divEq`.

* **§2 — the family keystone.**  `divFam_divEq_of_stalkIdeal_eq` (fully proven) descends
  §1 to the setoid quotient `DivFam` (`DivFam.mk_eq_mk_iff`).  The pinned deliverable
  `divFam_divEq_of_eps_eq` takes the ε-pair equality `divFamEps … G = divFamEps … G'` and
  the **relative window→stalk-ideal mono** as a threaded named hypothesis `hbridge` — the
  one genuinely gated seam (see below).

## The threaded seam (`hbridge`) — DISCHARGED; the route below is DEAD

`hbridge` promises: equal ε-windows over `R` force equal stalk ideals of the two
equation systems at every point of `relCurve C R`.  It is DISCHARGED seam-free in
`AlgebraicJacobian.Picard.DivSchemeMonoBridgeRel` (`divFam_divEq_of_eps_eq_total`,
any commutative test ring) — but NOT by the route sketched below, which is
mathematically FALSE at its fibrewise→relative step (`t` vs `t+ε` over `k[ε]`: equal
stalk ideals in every fibre, distinct relative stalk ideals; I-0231).  The landed
mechanism consumes the ε-equality at the `R`-level via window recovery
(`CertifiedDivisorFamily.windowGen`).  The original sketch, kept for the record:

* fibrewise (residue field `κ(p)`, `p ∈ Spec R`, `R` Noetherian) the field mono
  `divFamDivisor_eq_of_divFamEps_fst_eq` (I-0214, `Picard/DivisorFamilyEpsMono.lean`)
  turns equal ε-windows into equal base divisors — hence equal stalk ideals in the
  fibre — through the DD-4 field-content dictionary `Φ` and the right-exactness seam
  `hsurj` (both still gated: the DD-4-residue lane D1/D2 for `hsurj`, I-0214's open `Φ`);
* the colon-Tor pair upgrades fibrewise stalk-ideal equality to relative:
  `Module.Flat.mem_colon_smul_top_of_smul_mem_smul_top` and
  `Module.Flat.mem_nonZeroDivisors_of_forall_tmul_residueField`
  (`Picard/FibrewiseRegular.lean`) with the flat-cokernel base change
  `tensorKer_bijective_of_flat_coker` / `includeRight_mem_nonZeroDivisors_of_flat_coker`
  (`Picard/FlatCokernel.lean`);
* the fibre-by-fibre statement uses the family base change `DivFam.mapAlg` (DD-1c, in
  flight) to present each fibre.

Per the DDR-8 route note, these gated inputs are **threaded**, not re-derived here: when
they land the fan-in into `hbridge` is mechanical.  Everything *downstream* of the
stalk-ideal equality — the general upgrade and the setoid descent — is fully proven in
this file, axiom-clean.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

/-! ## §1 The general upgrade: equal stalk ideals everywhere ⟹ `DivEq` -/

namespace Scheme.LocalEquations

variable {X : Scheme.{u}}

/-- **Mutual divisibility of a nonzerodivisor yields a unit factor**: if `a` is a
nonzerodivisor and each of `a`, `b` lies in the principal ideal generated by the other,
then `a = u · b` for a unit `u`.  The two cofactors multiply to `1` because `a` is
regular. -/
private lemma exists_unit_of_mem_span_both {S : Type u} [CommRing S] {a b : S}
    (ha : a ∈ nonZeroDivisors S)
    (hab : a ∈ Ideal.span {b}) (hba : b ∈ Ideal.span {a}) :
    ∃ u : Sˣ, a = (u : S) * b := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hab
  obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton'.mp hba
  have hself : a = (c * c') * a := by rw [mul_assoc, hc', hc]
  have hzero : (c * c' - 1) * a = 0 := by rw [sub_mul, one_mul, ← hself, sub_self]
  have hcc : c * c' = 1 := sub_eq_zero.mp ((mul_right_mem_nonZeroDivisors_eq_zero_iff ha).mp hzero)
  exact ⟨⟨c, c', hcc, by rw [mul_comm]; exact hcc⟩, by rw [← hc, mul_comm]⟩

/-- **The general upgrade** (DDR-8 §1; the base-free "relative unit ⟹ `DivEq`" step): if
two local-equation systems have the same stalk ideal at every point then they are
divisor-equal.  On the common refinement `d₁.cover ⊓ d₂.cover` each equation's germ lies
in the span of the other's germ at every point (the stalk ideals coincide,
`germ_eqn_span_eq`), so by stalk-locality of regular principal ideals
(`Scheme.mem_span_singleton_of_forall_germ`) each restricted equation divides the other
over the whole piece; the two equations are nonzerodivisors, so the cofactor is a unit
(`exists_unit_of_mem_span_both`).  This is the exact converse of `stalkIdeal_eq_of_divEq`. -/
theorem divEq_of_stalkIdeal_eq {d₁ d₂ : X.LocalEquations}
    (h : ∀ z : X, d₁.stalkIdeal z = d₂.stalkIdeal z) : d₁.DivEq d₂ := by
  refine ⟨d₁.cover ⊓ d₂.cover, inf_le_left, inf_le_right, fun x => ?_⟩
  have hle₁ : (d₁.cover ⊓ d₂.cover).opens x ≤ d₁.cover.opens x := inf_le_left
  have hle₂ : (d₁.cover ⊓ d₂.cover).opens x ≤ d₂.cover.opens x := inf_le_right
  set a : Γ(X, (d₁.cover ⊓ d₂.cover).opens x) :=
    (X.presheaf.map (homOfLE hle₁).op).hom (d₁.eqn x) with ha_def
  set b : Γ(X, (d₁.cover ⊓ d₂.cover).opens x) :=
    (X.presheaf.map (homOfLE hle₂).op).hom (d₂.eqn x) with hb_def
  have hga : ∀ (z : X) (hz : z ∈ (d₁.cover ⊓ d₂.cover).opens x),
      (X.presheaf.germ _ z hz).hom a
        = (X.presheaf.germ (d₁.cover.opens x) z (hle₁ hz)).hom (d₁.eqn x) := by
    intro z hz; rw [ha_def, TopCat.Presheaf.germ_res_apply]
  have hgb : ∀ (z : X) (hz : z ∈ (d₁.cover ⊓ d₂.cover).opens x),
      (X.presheaf.germ _ z hz).hom b
        = (X.presheaf.germ (d₂.cover.opens x) z (hle₂ hz)).hom (d₂.eqn x) := by
    intro z hz; rw [hb_def, TopCat.Presheaf.germ_res_apply]
  have hareg : ∀ (z : X) (hz : z ∈ (d₁.cover ⊓ d₂.cover).opens x),
      (X.presheaf.germ _ z hz).hom a ∈ nonZeroDivisors (X.presheaf.stalk z) := by
    intro z hz; rw [hga z hz]; exact d₁.regular x z (hle₁ hz)
  have hbreg : ∀ (z : X) (hz : z ∈ (d₁.cover ⊓ d₂.cover).opens x),
      (X.presheaf.germ _ z hz).hom b ∈ nonZeroDivisors (X.presheaf.stalk z) := by
    intro z hz; rw [hgb z hz]; exact d₂.regular x z (hle₂ hz)
  have hab : a ∈ Ideal.span {b} := by
    refine Scheme.mem_span_singleton_of_forall_germ hbreg (fun z hz => ?_)
    rw [hga z hz, hgb z hz, germ_eqn_span_eq d₂ x z (hle₂ hz), ← h z,
      ← germ_eqn_span_eq d₁ x z (hle₁ hz)]
    exact Ideal.mem_span_singleton_self _
  have hba : b ∈ Ideal.span {a} := by
    refine Scheme.mem_span_singleton_of_forall_germ hareg (fun z hz => ?_)
    rw [hgb z hz, hga z hz, germ_eqn_span_eq d₁ x z (hle₁ hz), h z,
      ← germ_eqn_span_eq d₂ x z (hle₂ hz)]
    exact Ideal.mem_span_singleton_self _
  have haNZD : a ∈ nonZeroDivisors Γ(X, (d₁.cover ⊓ d₂.cover).opens x) := by
    rw [ha_def]; exact d₁.eqn_restrict_mem_nonZeroDivisors x hle₁
  exact exists_unit_of_mem_span_both haNZD hab hba

end Scheme.LocalEquations

/-! ## §2 The family keystone: the relative mono of `ε` -/

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsFinite π]

noncomputable local instance instOverCleftMono : C.left.Over (Spec (.of k)) := ⟨C.hom⟩

/-- **The relative mono, stalk-ideal form** (fully proven): two certified divisor families
over `R` whose underlying equation systems have the same stalk ideal at every point of
`relCurve C R` are equal in `DivFam` — descend the general upgrade
(`Scheme.LocalEquations.divEq_of_stalkIdeal_eq`) through the setoid
(`DivFam.mk_eq_mk_iff`). -/
theorem divFam_divEq_of_stalkIdeal_eq (g : ℕ) (G G' : CertifiedDivisorFamily C R π g)
    (hstalk : ∀ z : relCurve C R, G.eqns.stalkIdeal z = G'.eqns.stalkIdeal z) :
    DivFam.mk G = DivFam.mk G' :=
  DivFam.mk_eq_mk_iff.mpr (Scheme.LocalEquations.divEq_of_stalkIdeal_eq hstalk)

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))] [QuasiCompact (C.left ↘ Spec (.of k))]
  [IsDominant π]
variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hπ : π ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))

/-- **The relative mono / Law-1 core** (DDR-8, `informal/spec-dd-r.md` §3 item 7): two
certified divisor families of degree `g` over the test ring `R` whose embedding pairs `ε`
agree are equal in `DivFam`.

The mono content — that equal ε-windows over `R` force equal stalk ideals at every point
— is the colon-Tor discharge of the fibrewise field mono
(`divFamDivisor_eq_of_divFamEps_fst_eq`, I-0214) and is threaded as the named seam
`hbridge` (gated on the DD-4-residue `hsurj`, I-0214's `Φ`, and the in-flight family base
change `DivFam.mapAlg`; `R` Noetherian; see the file header).  Given the seam, the
divisor equality is the general upgrade `divFam_divEq_of_stalkIdeal_eq`, fully proven
above. -/
theorem divFam_divEq_of_eps_eq (g : ℕ) (G G' : CertifiedDivisorFamily C R π g)
    (heps : divFamEps hπ g (DivFam.mk G) = divFamEps hπ g (DivFam.mk G'))
    (hbridge : divFamEps hπ g (DivFam.mk G) = divFamEps hπ g (DivFam.mk G') →
      ∀ z : relCurve C R, G.eqns.stalkIdeal z = G'.eqns.stalkIdeal z) :
    DivFam.mk G = DivFam.mk G' :=
  divFam_divEq_of_stalkIdeal_eq g G G' (hbridge heps)

end AlgebraicGeometry
