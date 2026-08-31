/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.RigidEngine5Toolkit
import AlgebraicJacobian.Picard.DivSchemeFamily
import Mathlib.RingTheory.Support

/-!
# DD-4 redesign — the ann-based fibre-cutter engine (`h z ∈ ann(N z)`)

The genuine-geometry core of the DD-4 seed redesign (`informal/spec-dd4-redesign.md` §1.3,
landing note I-0289): the seed's `h z` must be a **genuine fibre-cutter**, an element of
`ann(N z)` where `N z = J z / (read sec z)` is the base-ideal colength module at `z`.  The
old `h z = algebraMap f` (base-only pullback, `DivSchemeSeedUnivGen.lean:289`) made `D(h z)`
the *whole* fibre chart (I-0288 fact 2), so I-0288's razor `hle` demanded achievement on the
entire chart — impossible.  An `ann(N z)` element is a genuine cutter: on `D(h z)` the base
ideal `J z` collapses to `⟨read sec z⟩`, so the divisibility clause `hdvd` holds *directly*.

Probe (I-0289 §2): NO fibre-cutter over a general test ring `R` exists in-tree — the only
in-tree point-in-fibre cutter is `PointDivisor.pointSec` over a *field* base.  `ann(N z)` is
the in-tree route to a genuine *relative* fibre-cutter, built here from the mathlib support
theory (`Module.support_eq_zeroLocus`, `Module.mem_support_iff_of_finite`) at the point
`z ∉ supp(N z)`.

## What this file lands (the reusable engine, `z ∉ supp(N z)` taken as hypothesis)

* `exists_mem_annihilator_notMem_of_notMem_support` — **the pure commutative-algebra core**:
  for a finite `A`-module `N` and a prime `p ∉ supp N`, an annihilator element `h ∈ ann N`
  with `h ∉ p` (from `Module.mem_support_iff_of_finite` + `SetLike.not_le_iff_exists`).

* `IsAffineOpen.exists_mem_basicOpen_forall_smul_eq_zero` — **the fibre-cutter existence**:
  on an affine open `V`, at a point `z ∈ V` with the module-stalk prime
  `primeIdealOf z ∉ supp N` (a finite `Γ(X,V)`-module `N`), a section `h ∈ Γ(X,V)` with
  `z ∈ D(h)` and `h` annihilating `N`.  This is the ann-based `h z`, with `z ∈ D(h z)`.

* `Scheme.resHom_mem_span_singleton_of_mul_mem` — **the DIRECT divisibility engine**: if
  `h * s ∈ ⟨e⟩` globally, then on the basic open `D(h)` (where `h` is a unit) the restriction
  of `s` lies in `⟨e⟩`.  Applied with `s = read ψ`, `e = read sec z`: the ann containment
  `h · J z ⊆ ⟨read sec z⟩` yields `read ψ ∈ ⟨read sec z⟩` on `D(h z)` — I-0289's *DIRECT*
  `hdvd`, no per-fibre `hfield`/Nakayama decomposition.

The point hypothesis `z ∉ supp(N z)` is exactly the relative-local-BPF Nakayama `RD-N`
(`read sec z` generates `J z` at the stalk `𝒪_z`, brick 3), gated on brick 1's `J z`-flatness;
this file takes it as a hypothesis so the fibre-cutter is non-circular and forward-compatible
with the redesigned seed (the pattern of bricks 1/2).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

/-! ## The pure commutative-algebra core -/

/-- **An annihilator element off a support-free prime** (the ann-cutter's algebraic heart):
for a finite `A`-module `N` and a prime `p` not in the support of `N`, there is
`h ∈ ann N` with `h ∉ p`.  Directly from `Module.mem_support_iff_of_finite`
(`p ∈ supp N ↔ ann N ≤ p`) and `SetLike.not_le_iff_exists`. -/
theorem exists_mem_annihilator_notMem_of_notMem_support {A : Type u} [CommRing A]
    (N : Type u) [AddCommGroup N] [Module A N] [Module.Finite A N]
    {p : PrimeSpectrum A} (hp : p ∉ Module.support A N) :
    ∃ h : A, h ∈ Module.annihilator A N ∧ h ∉ p.asIdeal := by
  rw [Module.mem_support_iff_of_finite] at hp
  exact SetLike.not_le_iff_exists.mp hp

/-! ## The fibre-cutter existence on an affine open -/

/-- **The ann-based fibre-cutter** (redesign brick 3, `informal/spec-dd4-redesign.md` §1.3):
on an affine open `V` of `X`, at a point `z ∈ V` whose module-stalk prime
`primeIdealOf ⟨z, hz⟩` lies outside the support of a finite `Γ(X,V)`-module `N`, there is a
section `h ∈ Γ(X,V)` with `z ∈ D(h)` and `h · N = 0`.  With `N = J z / ⟨read sec z⟩`, the
`z ∉ supp N` hypothesis is the stalk generation `RD-N` (`read sec z` generates `J z` at
`𝒪_z`, since the achiever cuts exactly `d_p` at `z`, so `z` is not an extra zero); the
output `h ∈ ann N` cuts a genuine fibre-neighbourhood `D(h)` on which `J z = ⟨read sec z⟩`.
The point→prime translation is `IsAffineOpen.primeIdealOf` / `fromSpec_primeIdealOf`. -/
theorem IsAffineOpen.exists_mem_basicOpen_forall_smul_eq_zero {X : Scheme.{u}}
    {V : X.Opens} (hV : IsAffineOpen V) (N : Type u) [AddCommGroup N] [Module Γ(X, V) N]
    [Module.Finite Γ(X, V) N] {z : X} (hz : z ∈ V)
    (hsupp : hV.primeIdealOf ⟨z, hz⟩ ∉ Module.support Γ(X, V) N) :
    ∃ h : Γ(X, V), z ∈ X.basicOpen h ∧ ∀ n : N, h • n = 0 := by
  obtain ⟨h, hann, hnp⟩ := exists_mem_annihilator_notMem_of_notMem_support N hsupp
  refine ⟨h, ?_, Module.mem_annihilator.mp hann⟩
  have hp : hV.primeIdealOf ⟨z, hz⟩ ∈ PrimeSpectrum.basicOpen h :=
    (PrimeSpectrum.mem_basicOpen h _).mpr hnp
  rw [← hV.fromSpec_preimage_basicOpen h, Scheme.Hom.mem_preimage] at hp
  rwa [hV.fromSpec_primeIdealOf ⟨z, hz⟩] at hp

/-! ## The DIRECT divisibility engine on a basic open -/

/-- **DIRECT divisibility from an annihilator containment** (redesign brick 3, the DIRECT
`hdvd`): if `h * s ∈ ⟨e⟩` in `Γ(X, U)`, then the restriction of `s` to the basic open
`D(h)` lies in `⟨e⟩` there (`h` restricts to a *unit* on `D(h)`, so the cofactor divides
through).  Applied with `h ∈ ann(J z / ⟨read sec z⟩)` (so `h · read ψ ∈ ⟨read sec z⟩`),
`s = read ψ`, `e = read sec z`, this is exactly the seed's divisibility clause on `D(h z)`
— DIRECT, without any per-fibre `hfield` or Nakayama-over-the-piece decomposition. -/
theorem Scheme.resHom_mem_span_singleton_of_mul_mem {X : Scheme.{u}} {U : X.Opens}
    (h e s : Γ(X, U)) (hmul : h * s ∈ Ideal.span {e}) :
    X.resHom (X.basicOpen_le h) s ∈ Ideal.span {X.resHom (X.basicOpen_le h) e} := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hmul
  obtain ⟨u, hu⟩ := Scheme.isUnit_resHom_of_eq_basicOpen h rfl (X.basicOpen_le h)
  have hres : X.resHom (X.basicOpen_le h) (h * s) = X.resHom (X.basicOpen_le h) (e * c) := by
    rw [hc]
  rw [map_mul, map_mul, ← hu] at hres
  rw [Ideal.mem_span_singleton]
  refine ⟨(↑u⁻¹ : Γ(X, X.basicOpen h)) * X.resHom (X.basicOpen_le h) c, ?_⟩
  calc X.resHom (X.basicOpen_le h) s
      = (↑u⁻¹ * ↑u) * X.resHom (X.basicOpen_le h) s := by rw [Units.inv_mul, one_mul]
    _ = ↑u⁻¹ * (↑u * X.resHom (X.basicOpen_le h) s) := by rw [mul_assoc]
    _ = ↑u⁻¹ * (X.resHom (X.basicOpen_le h) e * X.resHom (X.basicOpen_le h) c) := by rw [hres]
    _ = X.resHom (X.basicOpen_le h) e * (↑u⁻¹ * X.resHom (X.basicOpen_le h) c) := by ring

/-! ## The seed-shaped consumable: the DIRECT `hdvd` clause from the ann containment -/

namespace ThetaGeneratorSeed

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsFinite π] {a : ℕ}
variable {K : Submodule R (relThetaSections C R π a)}

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

/-- **`seedUniv'_h_fibre_cuts` — the DIRECT `hdvd` from the ann-based fibre-cutter**
(redesign brick 3, `informal/spec-dd4-redesign.md` §1.3): if at every point `z` the seed's
cutter `h z` annihilates the base-ideal colength — i.e. `h z · (read ψ) ∈ ⟨read (sec z)⟩` in
the *chart* `Γ(relPinnedChart (side z))` for every `ψ ∈ K` — then the seed's divisibility
clause `hdvd` holds on every piece `D(h z)`.  This feeds `isGenerator_of_fibre_ne_zero`
(`DivSchemeSeed.lean:188`) directly: `h z` restricts to a unit on `D(h z)`, so the base
ideal `J z` collapses to `⟨eqn z⟩` there.  No per-fibre `hfield`, no
`isGenerator_of_fibrewise_ker_span_of_field_vanishing` capstone — the whole `hdvd` wall is
dissolved by the ann containment (whose `z ∉ supp(N z)` premise is `RD-N`). -/
theorem hdvd_of_forall_smul_relThetaResSide_mem_span
    (D : ThetaGeneratorSeed C R π a K)
    (hann : ∀ (z : relCurve C R) ⦃ψ : relThetaSections C R π a⦄, ψ ∈ K →
      D.h z * relThetaResSide a (D.side z) le_rfl ψ
        ∈ Ideal.span {relThetaResSide a (D.side z) le_rfl (D.sec z)}) :
    ∀ (z : relCurve C R) ⦃ψ : relThetaSections C R π a⦄, ψ ∈ K →
      relThetaResSide a (D.side z) (D.piece_le z) ψ ∈ Ideal.span {D.eqn z} := by
  intro z ψ hψ
  rw [show relThetaResSide a (D.side z) (D.piece_le z) ψ
        = (relCurve C R).resHom ((relCurve C R).basicOpen_le (D.h z))
            (relThetaResSide a (D.side z) le_rfl ψ) from
      (resHom_relThetaResSide a (D.side z) le_rfl (D.piece_le z) ψ).symm,
    show D.eqn z = (relCurve C R).resHom ((relCurve C R).basicOpen_le (D.h z))
            (relThetaResSide a (D.side z) le_rfl (D.sec z)) from
      (resHom_relThetaResSide a (D.side z) le_rfl (D.piece_le z) (D.sec z)).symm]
  exact Scheme.resHom_mem_span_singleton_of_mul_mem (D.h z)
    (relThetaResSide a (D.side z) le_rfl (D.sec z))
    (relThetaResSide a (D.side z) le_rfl ψ) (hann z hψ)

end ThetaGeneratorSeed

end AlgebraicGeometry
