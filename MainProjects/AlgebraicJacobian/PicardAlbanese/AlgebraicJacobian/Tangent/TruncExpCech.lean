/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Tangent.TruncExpUnits

/-!
# The two-chart Čech unit-cocycle engine (W5-T2, algebra layer)

The pure-algebra heart of the Kleiman §5 Thm 5.11 cocycle leg. A *two-chart datum* is a
pair of ring homomorphisms `ρ₁ : A₁ →+* B`, `ρ₂ : A₂ →+* B` — think `Aᵢ = Γ(Uᵢ, 𝒪_C)`
the section rings of a 2-affine cover and `B = Γ(U₀ ⊓ U₁, 𝒪_C)` the overlap ring, with
`ρᵢ` the restrictions. The two-cover Čech `Ȟ¹` of *units* is the quotient
`Bˣ ⧸ (im ρ₁ˣ · im ρ₂ˣ)` of transition units by coboundaries — the Picard group of the
cover in Čech form. Applying the same construction to the dual-number thickening
(`Aᵢ[ε] →+* B[ε]` via `TruncExpCech.mapRingHom`) and reducing mod `ε` (`unitsFst`, which
maps coboundaries to coboundaries) gives the restriction map `Ȟ¹ˣ(B[ε]) →* Ȟ¹ˣ(B)` of
`Pic(C_ε) → Pic(C)`.

The engine computes the **kernel** of that reduction: the truncated exponential
`b ↦ [1 + b ε]` induces an additive equivalence

```
B ⧸ (ρ₁(A₁) + ρ₂(A₂))  ≃+  ker(Ȟ¹ˣ(B[ε]) → Ȟ¹ˣ(B))
```

(`truncExpCechKernelAddEquiv`), whose source is exactly the two-chart Čech cokernel
shape of `AlgebraicGeometry.TwoCover.H1Cok` (`Γ(U₀ ⊓ U₁) ⧸ range diff`) — i.e.
`H¹(C, 𝒪_C)` on a curve; the carrier assembly is
`AlgebraicJacobian.Tangent.TruncExpCechH1`. Equivariance for the Mumford `ε ↦ tε`
scaling (`scaleRingHom`) is provided pointwise: `unitsScale_mk_truncExpUnit` shows the
scaling acts on truncated-exponential classes as `b ↦ t·b`, matching the `k`-scalar
action on `H1Cok`.

**Design note (the `(a+b)•x` distributivity trap, worksheet D6 / recon R5(iii))**: no
`SMul`/`Module` structure is ever placed on the units-kernel side. All `k`-linearity
bookkeeping stays on the Čech-cokernel side `B ⧸ (ρ₁A₁ + ρ₂A₂)`, where it is the honest
module structure of a quotient of section modules; the Mumford scaling is related to it
only through the pointwise equivariance lemmas above. In particular the old draft's
unproved scalar distributivity for the functorial scaling action is *dodged*, not
needed.

Everything here is elementary commutative algebra: no schemes, no sheaves. Ported
(Wave-5 brick T2, stage 1) from the old draft's
`Algebraic-Jacobian-Challenge/AlgebraicJacobian/Picard/Pic0DualNumberCocycle.lean` §6,
re-proved against the Rebuild's pin, in the collision-safe project namespace
`TruncExpCech` (see `AlgebraicJacobian.Tangent.TruncExpUnits`).

## Main declarations

* `TruncExpCech.cechCoboundaryUnits ρ₁ ρ₂ : Subgroup Bˣ` — the coboundary subgroup
  `im(ρ₁ˣ) · im(ρ₂ˣ)`, so `Bˣ ⧸ cechCoboundaryUnits` is the two-cover Čech `Ȟ¹` of
  units.
* `TruncExpCech.cechCoboundaryAdd ρ₁ ρ₂ : AddSubgroup B` — the additive coboundaries
  `ρ₁(A₁) + ρ₂(A₂)`.
* `TruncExpCech.cechUnitsReduction ρ₁ ρ₂ : Ȟ¹ˣ(B[ε]) →* Ȟ¹ˣ(B)` — reduction mod `ε`.
* `TruncExpCech.truncExpCechKernelAddEquiv :
  B ⧸ cechCoboundaryAdd ρ₁ ρ₂ ≃+ Additive (cechUnitsReduction ρ₁ ρ₂).ker` — the
  keystone kernel computation.
* `TruncExpCech.unitsScale_mk_truncExpUnit`,
  `TruncExpCech.cechCoboundaryUnits_le_comap_unitsScale` — Mumford-scaling
  equivariance.

## References

Kleiman, "The Picard scheme", §5, proof of Thm 5.11 (arXiv:math/0504020); Mumford,
"Abelian varieties", §II.4.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u v w

namespace TruncExpCech

open TrivSqZeroExt DualNumber

variable {A₁ : Type u} {A₂ : Type v} {B : Type w}
variable [CommRing A₁] [CommRing A₂] [CommRing B]

/-! ## The coboundary subgroups of a two-chart datum -/

/-- **The Čech coboundary subgroup of a two-chart datum**: for restriction
homomorphisms `ρ₁ : A₁ →+* B`, `ρ₂ : A₂ →+* B` onto the overlap ring `B`, the subgroup
`im(ρ₁ˣ) · im(ρ₂ˣ) ≤ Bˣ` of transition units that are coboundaries of the 2-cover. The
quotient `Bˣ ⧸ cechCoboundaryUnits ρ₁ ρ₂` is the two-cover Čech `Ȟ¹` of units — the
Čech-cocycle Picard group of the cover. -/
def cechCoboundaryUnits (ρ₁ : A₁ →+* B) (ρ₂ : A₂ →+* B) : Subgroup Bˣ :=
  (Units.map ρ₁.toMonoidHom).range ⊔ (Units.map ρ₂.toMonoidHom).range

/-- Membership in the Čech coboundary subgroup: `u` is a coboundary iff
`u = ρ₁ˣ(v₁) · ρ₂ˣ(v₂)` for chart units `vᵢ ∈ Aᵢˣ` (the sign convention with a product
rather than a quotient is immaterial: the ranges are subgroups). -/
theorem mem_cechCoboundaryUnits {ρ₁ : A₁ →+* B} {ρ₂ : A₂ →+* B} {u : Bˣ} :
    u ∈ cechCoboundaryUnits ρ₁ ρ₂
      ↔ ∃ (v₁ : A₁ˣ) (v₂ : A₂ˣ),
          Units.map ρ₁.toMonoidHom v₁ * Units.map ρ₂.toMonoidHom v₂ = u := by
  constructor
  · intro h
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp h
    obtain ⟨v₁, rfl⟩ := MonoidHom.mem_range.mp hy
    obtain ⟨v₂, rfl⟩ := MonoidHom.mem_range.mp hz
    exact ⟨v₁, v₂, rfl⟩
  · rintro ⟨v₁, v₂, rfl⟩
    exact Subgroup.mem_sup.mpr
      ⟨_, MonoidHom.mem_range.mpr ⟨v₁, rfl⟩, _, MonoidHom.mem_range.mpr ⟨v₂, rfl⟩, rfl⟩

/-- Chart units from the first chart are coboundaries. -/
theorem unitsMap_mem_cechCoboundaryUnits_left (ρ₁ : A₁ →+* B) (ρ₂ : A₂ →+* B)
    (v : A₁ˣ) : Units.map ρ₁.toMonoidHom v ∈ cechCoboundaryUnits ρ₁ ρ₂ :=
  mem_cechCoboundaryUnits.mpr ⟨v, 1, by simp⟩

/-- Chart units from the second chart are coboundaries. -/
theorem unitsMap_mem_cechCoboundaryUnits_right (ρ₁ : A₁ →+* B) (ρ₂ : A₂ →+* B)
    (v : A₂ˣ) : Units.map ρ₂.toMonoidHom v ∈ cechCoboundaryUnits ρ₁ ρ₂ :=
  mem_cechCoboundaryUnits.mpr ⟨1, v, by simp⟩

/-- **The additive Čech coboundary subgroup of a two-chart datum**:
`ρ₁(A₁) + ρ₂(A₂) ≤ B` as an additive subgroup. The quotient
`B ⧸ cechCoboundaryAdd ρ₁ ρ₂` is the two-cover Čech cokernel — for the section rings of
a 2-affine cover, exactly the carrier shape of `AlgebraicGeometry.TwoCover.H1Cok`
(`Γ(U₀ ⊓ U₁) ⧸ range diff`; a difference `ρ₁ a₁ - ρ₂ a₂` and a sum `ρ₁ a₁ + ρ₂ a₂` span
the same subgroup). -/
def cechCoboundaryAdd (ρ₁ : A₁ →+* B) (ρ₂ : A₂ →+* B) : AddSubgroup B :=
  ρ₁.toAddMonoidHom.range ⊔ ρ₂.toAddMonoidHom.range

/-- Membership in the additive Čech coboundary subgroup. -/
theorem mem_cechCoboundaryAdd {ρ₁ : A₁ →+* B} {ρ₂ : A₂ →+* B} {b : B} :
    b ∈ cechCoboundaryAdd ρ₁ ρ₂ ↔ ∃ (a₁ : A₁) (a₂ : A₂), ρ₁ a₁ + ρ₂ a₂ = b := by
  constructor
  · intro h
    obtain ⟨y, hy, z, hz, rfl⟩ := AddSubgroup.mem_sup.mp h
    obtain ⟨a₁, rfl⟩ := AddMonoidHom.mem_range.mp hy
    obtain ⟨a₂, rfl⟩ := AddMonoidHom.mem_range.mp hz
    exact ⟨a₁, a₂, rfl⟩
  · rintro ⟨a₁, a₂, rfl⟩
    exact AddSubgroup.mem_sup.mpr
      ⟨_, AddMonoidHom.mem_range.mpr ⟨a₁, rfl⟩, _, AddMonoidHom.mem_range.mpr ⟨a₂, rfl⟩, rfl⟩

/-- Differences of chart sections are additive Čech coboundaries — the subtraction form
of membership, matching the difference-of-restrictions map
`AlgebraicGeometry.TwoCover.diff` of the geometric consumer. Clean-binder helper: state
and use this on abstract rings, then transport the result along the (defeq) carrier
identifications of the sheaf dialect. -/
theorem sub_mem_cechCoboundaryAdd (ρ₁ : A₁ →+* B) (ρ₂ : A₂ →+* B)
    (a₁ : A₁) (a₂ : A₂) :
    ρ₁ a₁ - ρ₂ a₂ ∈ cechCoboundaryAdd ρ₁ ρ₂ :=
  mem_cechCoboundaryAdd.mpr ⟨a₁, -a₂, by rw [map_neg, ← sub_eq_add_neg]⟩

/-- Additive Čech coboundaries are differences of chart sections — the subtraction form
of the membership characterisation (converse of `sub_mem_cechCoboundaryAdd`). -/
theorem exists_sub_of_mem_cechCoboundaryAdd {ρ₁ : A₁ →+* B} {ρ₂ : A₂ →+* B}
    {b : B} (h : b ∈ cechCoboundaryAdd ρ₁ ρ₂) :
    ∃ (a₁ : A₁) (a₂ : A₂), ρ₁ a₁ - ρ₂ a₂ = b := by
  obtain ⟨a₁, a₂, ha⟩ := mem_cechCoboundaryAdd.mp h
  exact ⟨a₁, -a₂, by rw [map_neg, sub_neg_eq_add, ha]⟩

/-! ## The truncated exponential detects the additive coboundaries -/

/-- **The truncated exponential detects the additive coboundaries** (the
well-definedness/injectivity heart of the Kleiman §5 Thm 5.11 cocycle leg): the unit
`1 + b ε` on the dual-number overlap ring is a coboundary of the thickened cover iff
`b` is an additive coboundary `ρ₁(a₁) + ρ₂(a₂)`.

Forward direction: decompose the two chart units `wᵢ ∈ (Aᵢ[ε])ˣ` as
`inl(wᵢ₀)·(1 + cᵢ ε)` (`unitsInl_unitsFst_mul_truncExpUnit`); reducing the coboundary
relation mod `ε` forces the constant parts to cancel, leaving
`1 + b ε = 1 + (ρ₁ c₁ + ρ₂ c₂) ε`. -/
theorem truncExpUnit_mem_cechCoboundaryUnits_iff
    (ρ₁ : A₁ →+* B) (ρ₂ : A₂ →+* B) (b : B) :
    truncExpUnit b ∈ cechCoboundaryUnits (mapRingHom ρ₁) (mapRingHom ρ₂)
      ↔ b ∈ cechCoboundaryAdd ρ₁ ρ₂ := by
  constructor
  · intro h
    obtain ⟨w₁, w₂, hw⟩ := mem_cechCoboundaryUnits.mp h
    rw [← unitsInl_unitsFst_mul_truncExpUnit w₁,
      ← unitsInl_unitsFst_mul_truncExpUnit w₂, map_mul, map_mul,
      unitsMap_mapRingHom_unitsInl, unitsMap_mapRingHom_unitsInl,
      map_mapRingHom_truncExpUnit, map_mapRingHom_truncExpUnit,
      mul_mul_mul_comm, ← map_mul, ← truncExpUnit_add] at hw
    -- reduce mod `ε`: the constant part of the coboundary is trivial
    have hfst := congrArg unitsFst hw
    rw [map_mul, unitsFst_unitsInl, unitsFst_truncExpUnit, mul_one,
      unitsFst_truncExpUnit] at hfst
    rw [hfst, map_one, one_mul] at hw
    exact mem_cechCoboundaryAdd.mpr ⟨_, _, truncExpUnit_injective hw⟩
  · intro h
    obtain ⟨a₁, a₂, rfl⟩ := mem_cechCoboundaryAdd.mp h
    refine mem_cechCoboundaryUnits.mpr ⟨truncExpUnit a₁, truncExpUnit a₂, ?_⟩
    rw [map_mapRingHom_truncExpUnit, map_mapRingHom_truncExpUnit, ← truncExpUnit_add]

/-! ## The Čech reduction map and its kernel -/

/-- Reduction mod `ε` on units carries thickened coboundaries to coboundaries
(`unitsFst` naturality), so it descends to the Čech `Ȟ¹` quotients. -/
theorem cechCoboundaryUnits_le_comap_unitsFst (ρ₁ : A₁ →+* B) (ρ₂ : A₂ →+* B) :
    cechCoboundaryUnits (mapRingHom ρ₁) (mapRingHom ρ₂) ≤
      (cechCoboundaryUnits ρ₁ ρ₂).comap (unitsFst (R := B)) := by
  intro u hu
  obtain ⟨w₁, w₂, rfl⟩ := mem_cechCoboundaryUnits.mp hu
  refine Subgroup.mem_comap.mpr (mem_cechCoboundaryUnits.mpr
    ⟨unitsFst w₁, unitsFst w₂, ?_⟩)
  rw [map_mul, unitsFst_map_mapRingHom, unitsFst_map_mapRingHom]

/-- **The reduction map of two-chart Čech `Ȟ¹`-of-units groups**
`Ȟ¹ˣ(B[ε]) →* Ȟ¹ˣ(B)` induced by reduction mod `ε` — the Čech-cocycle incarnation of
the restriction `Pic(C ×_k Spec k[ε]) → Pic(C)` along `ε ↦ 0`. Its kernel is computed
by `truncExpCechKernelAddEquiv` below. -/
noncomputable def cechUnitsReduction (ρ₁ : A₁ →+* B) (ρ₂ : A₂ →+* B) :
    ((B[ε])ˣ ⧸ cechCoboundaryUnits (mapRingHom ρ₁) (mapRingHom ρ₂)) →*
      Bˣ ⧸ cechCoboundaryUnits ρ₁ ρ₂ :=
  QuotientGroup.map _ _ (unitsFst (R := B))
    (cechCoboundaryUnits_le_comap_unitsFst ρ₁ ρ₂)

/-- Truncated-exponential classes lie in the kernel of the Čech reduction map:
`1 + b ε` reduces to `1` mod `ε`. -/
theorem cechUnitsReduction_mk_truncExpUnit (ρ₁ : A₁ →+* B) (ρ₂ : A₂ →+* B)
    (b : B) :
    cechUnitsReduction ρ₁ ρ₂ (QuotientGroup.mk (truncExpUnit b)) = 1 := by
  rw [cechUnitsReduction, QuotientGroup.map_mk, unitsFst_truncExpUnit,
    QuotientGroup.mk_one]

/-- Vanishing of a truncated-exponential class in the thickened Čech `Ȟ¹`:
`[1 + b ε] = 1` iff `b` is an additive coboundary. -/
theorem mk_truncExpUnit_eq_one_iff (ρ₁ : A₁ →+* B) (ρ₂ : A₂ →+* B) (b : B) :
    (QuotientGroup.mk (truncExpUnit b) :
        (B[ε])ˣ ⧸ cechCoboundaryUnits (mapRingHom ρ₁) (mapRingHom ρ₂)) = 1
      ↔ b ∈ cechCoboundaryAdd ρ₁ ρ₂ := by
  rw [QuotientGroup.eq_one_iff]
  exact truncExpUnit_mem_cechCoboundaryUnits_iff ρ₁ ρ₂ b

/-- **Every kernel class of the Čech reduction is a truncated exponential** (the
surjectivity heart of the Kleiman §5 Thm 5.11 cocycle leg): a class of `Ȟ¹ˣ(B[ε])`
restricting trivially mod `ε` is represented by `1 + b ε` for some `b : B`. Proof:
normalise a representative `u` by the (lifted) chart units trivialising its reduction;
the corrected unit has trivial constant part, hence lies in the range of the truncated
exponential (`truncExp_range_eq_ker_unitsFst`). -/
theorem exists_mk_truncExpUnit_of_cechUnitsReduction_eq_one
    (ρ₁ : A₁ →+* B) (ρ₂ : A₂ →+* B)
    (x : (B[ε])ˣ ⧸ cechCoboundaryUnits (mapRingHom ρ₁) (mapRingHom ρ₂))
    (hx : cechUnitsReduction ρ₁ ρ₂ x = 1) :
    ∃ b : B, (QuotientGroup.mk (truncExpUnit b) :
      (B[ε])ˣ ⧸ cechCoboundaryUnits (mapRingHom ρ₁) (mapRingHom ρ₂)) = x := by
  revert hx
  induction x using QuotientGroup.induction_on with
  | H u =>
    intro hu
    rw [cechUnitsReduction, QuotientGroup.map_mk, QuotientGroup.eq_one_iff] at hu
    obtain ⟨v₁, v₂, hv⟩ := mem_cechCoboundaryUnits.mp hu
    -- the chart-unit correction of `u`
    have hker : unitsFst
        ((Units.map (mapRingHom ρ₁).toMonoidHom (unitsInl v₁))⁻¹ * u *
          (Units.map (mapRingHom ρ₂).toMonoidHom (unitsInl v₂))⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, map_inv, unitsMap_mapRingHom_unitsInl,
        unitsMap_mapRingHom_unitsInl, unitsFst_unitsInl, unitsFst_unitsInl, ← hv]
      group
    have hmem : (Units.map (mapRingHom ρ₁).toMonoidHom (unitsInl v₁))⁻¹ * u *
        (Units.map (mapRingHom ρ₂).toMonoidHom (unitsInl v₂))⁻¹
          ∈ (truncExp (R := B)).range := by
      rw [truncExp_range_eq_ker_unitsFst]
      exact MonoidHom.mem_ker.mpr hker
    obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp hmem
    refine ⟨m.toAdd, ?_⟩
    rw [← truncExp_apply, hm, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv, QuotientGroup.mk_inv,
      (QuotientGroup.eq_one_iff _).mpr
        (unitsMap_mem_cechCoboundaryUnits_left (mapRingHom ρ₁) (mapRingHom ρ₂)
          (unitsInl v₁)),
      (QuotientGroup.eq_one_iff _).mpr
        (unitsMap_mem_cechCoboundaryUnits_right (mapRingHom ρ₁) (mapRingHom ρ₂)
          (unitsInl v₂))]
    simp

/-! ## The kernel computation -/

/-- The truncated exponential as a monoid homomorphism into the kernel of the Čech
reduction map (multiplicative source `Multiplicative B`). -/
noncomputable def truncExpCechKernelMonoidHom (ρ₁ : A₁ →+* B) (ρ₂ : A₂ →+* B) :
    Multiplicative B →* (cechUnitsReduction ρ₁ ρ₂).ker where
  toFun b :=
    ⟨QuotientGroup.mk (truncExpUnit b.toAdd),
      MonoidHom.mem_ker.mpr (cechUnitsReduction_mk_truncExpUnit ρ₁ ρ₂ b.toAdd)⟩
  map_one' := Subtype.ext <| by
    change (QuotientGroup.mk (truncExpUnit ((1 : Multiplicative B).toAdd)) : _) = 1
    rw [toAdd_one, truncExpUnit_zero, QuotientGroup.mk_one]
  map_mul' b c := Subtype.ext <| by
    change (QuotientGroup.mk (truncExpUnit ((b * c).toAdd)) : _) = _
    rw [toAdd_mul, truncExpUnit_add, QuotientGroup.mk_mul]
    rfl

/-- **The truncated-exponential kernel computation** (Kleiman §5 Thm 5.11, cocycle leg,
algebra layer): for a two-chart datum `ρ₁ : A₁ →+* B`, `ρ₂ : A₂ →+* B`, the truncated
exponential `b ↦ [1 + b ε]` induces an additive equivalence

```
B ⧸ (ρ₁(A₁) + ρ₂(A₂))  ≃+  ker( Ȟ¹ˣ(B[ε]) →* Ȟ¹ˣ(B) )
```

from the two-cover Čech cokernel (the `AlgebraicGeometry.TwoCover.H1Cok` carrier
shape — `H¹(C, 𝒪_C)` for the section rings of a 2-affine cover of a curve) onto the
kernel of the dual-number Čech-units reduction (the two-chart
`ker(Pic(C_ε) → Pic(C))`). Well-definedness and injectivity are
`mk_truncExpUnit_eq_one_iff`; surjectivity is
`exists_mk_truncExpUnit_of_cechUnitsReduction_eq_one`; additivity is the
truncated-exponential functional equation `truncExpUnit_add`. -/
noncomputable def truncExpCechKernelAddEquiv (ρ₁ : A₁ →+* B) (ρ₂ : A₂ →+* B) :
    B ⧸ cechCoboundaryAdd ρ₁ ρ₂ ≃+
      Additive (cechUnitsReduction ρ₁ ρ₂).ker := by
  refine AddEquiv.ofBijective
    (QuotientAddGroup.lift (cechCoboundaryAdd ρ₁ ρ₂)
      (MonoidHom.toAdditiveRight (truncExpCechKernelMonoidHom ρ₁ ρ₂)) ?_) ⟨?_, ?_⟩
  · intro b hb
    apply Additive.toMul.injective
    apply Subtype.ext
    change (QuotientGroup.mk (truncExpUnit b) : _) = 1
    exact (mk_truncExpUnit_eq_one_iff ρ₁ ρ₂ b).mpr hb
  · rw [injective_iff_map_eq_zero]
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H b =>
      intro hbx
      have hb : (QuotientGroup.mk (truncExpUnit b) :
          (B[ε])ˣ ⧸ cechCoboundaryUnits (mapRingHom ρ₁) (mapRingHom ρ₂)) = 1 :=
        congrArg (fun y => (Additive.toMul y : (cechUnitsReduction ρ₁ ρ₂).ker).1) hbx
      rw [QuotientAddGroup.eq_zero_iff]
      exact (mk_truncExpUnit_eq_one_iff ρ₁ ρ₂ b).mp hb
  · intro y
    obtain ⟨b, hb⟩ := exists_mk_truncExpUnit_of_cechUnitsReduction_eq_one ρ₁ ρ₂
      (Additive.toMul y : (cechUnitsReduction ρ₁ ρ₂).ker).1
      (Additive.toMul y : (cechUnitsReduction ρ₁ ρ₂).ker).2
    exact ⟨QuotientAddGroup.mk b,
      Additive.toMul.injective (Subtype.ext hb)⟩

/-- Elementwise formula for the truncated-exponential kernel equivalence on residue
classes: `[b] ↦ [1 + b ε]`. Definitional. -/
theorem truncExpCechKernelAddEquiv_apply_mk (ρ₁ : A₁ →+* B) (ρ₂ : A₂ →+* B)
    (b : B) :
    ((Additive.toMul (truncExpCechKernelAddEquiv ρ₁ ρ₂ (QuotientAddGroup.mk b)) :
        (cechUnitsReduction ρ₁ ρ₂).ker) : _)
      = (QuotientGroup.mk (truncExpUnit b) :
          (B[ε])ˣ ⧸ cechCoboundaryUnits (mapRingHom ρ₁) (mapRingHom ρ₂)) :=
  rfl

/-! ## Mumford-scaling equivariance of the engine

The `ε ↦ tε` scaling of the overlap ring `B[ε]` (`scaleRingHom t`) preserves the
thickened coboundaries whenever the scalar is compatible with the charts
(`ρ₁ s₁ = t = ρ₂ s₂` — for a `k`-algebra datum, `sᵢ` and `t` are the images of a common
`a ∈ k`), hence descends to `Ȟ¹ˣ(B[ε])`, and it acts on truncated-exponential classes
exactly by `b ↦ t·b` — matching the `k`-scalar action on the Čech cokernel side of
`truncExpCechKernelAddEquiv`. -/

/-- The `ε ↦ tε` scaling preserves the thickened Čech coboundaries when the scalar `t`
is compatible with the charts (`ρ₁ s₁ = t = ρ₂ s₂`). -/
theorem cechCoboundaryUnits_le_comap_unitsScale (ρ₁ : A₁ →+* B) (ρ₂ : A₂ →+* B)
    {s₁ : A₁} {s₂ : A₂} {t : B} (h₁ : ρ₁ s₁ = t) (h₂ : ρ₂ s₂ = t) :
    cechCoboundaryUnits (mapRingHom ρ₁) (mapRingHom ρ₂) ≤
      (cechCoboundaryUnits (mapRingHom ρ₁) (mapRingHom ρ₂)).comap
        (Units.map (scaleRingHom t).toMonoidHom) := by
  intro u hu
  obtain ⟨w₁, w₂, rfl⟩ := mem_cechCoboundaryUnits.mp hu
  refine Subgroup.mem_comap.mpr (mem_cechCoboundaryUnits.mpr
    ⟨Units.map (scaleRingHom s₁).toMonoidHom w₁,
     Units.map (scaleRingHom s₂).toMonoidHom w₂, ?_⟩)
  rw [map_mul]
  congr 1
  · apply Units.ext
    simp only [Units.coe_map]
    exact (RingHom.congr_fun (mapRingHom_comp_scaleRingHom ρ₁ s₁) (w₁ : A₁[ε])).trans
      (by rw [h₁]; rfl)
  · apply Units.ext
    simp only [Units.coe_map]
    exact (RingHom.congr_fun (mapRingHom_comp_scaleRingHom ρ₂ s₂) (w₂ : A₂[ε])).trans
      (by rw [h₂]; rfl)

/-- **Equivariance of the truncated-exponential classes under the Mumford scaling**:
the `ε ↦ tε` scaling of `Ȟ¹ˣ(B[ε])` carries `[1 + b ε]` to `[1 + (t·b) ε]` — through
`truncExpCechKernelAddEquiv`, the scaling acts on the Čech cokernel
`B ⧸ (ρ₁(A₁) + ρ₂(A₂))` as multiplication by `t`, i.e. as the `k`-scalar action for a
`k`-algebra two-chart datum. -/
theorem unitsScale_mk_truncExpUnit (ρ₁ : A₁ →+* B) (ρ₂ : A₂ →+* B)
    {s₁ : A₁} {s₂ : A₂} {t : B} (h₁ : ρ₁ s₁ = t) (h₂ : ρ₂ s₂ = t) (b : B) :
    QuotientGroup.map _ _ (Units.map (scaleRingHom t).toMonoidHom)
        (cechCoboundaryUnits_le_comap_unitsScale ρ₁ ρ₂ h₁ h₂)
        (QuotientGroup.mk (truncExpUnit b))
      = (QuotientGroup.mk (truncExpUnit (t * b)) :
          (B[ε])ˣ ⧸ cechCoboundaryUnits (mapRingHom ρ₁) (mapRingHom ρ₂)) := by
  rw [QuotientGroup.map_mk, unitsScale_truncExpUnit]

end TruncExpCech
