/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeCertZarSep

/-!
# No-leak over a shrunken base, with no fibre hypothesis

The certificate assemblers consume, per piece `j`, the fibrewise clause

`∀ s, (fibre over s) ∩ closure (supp ∩ pieces j) ⊆ pieces j`

(`isCertified_of_noLeak_kernel_spanning`), equivalently emptiness of the **leak locus**
`supportLeak (pieces j) = closure (supp ∩ pieces j) \ pieces j`
(`Scheme.LocalEquations.isClosed_supportLocus_inter_iff_supportLeak_eq_empty`).

The `tube-fibre` leaf of the DD-R lane tried to obtain this by putting the whole support
inside a single piece.  That shape is refuted — `DivSchemeCertZarSep.lean`,
`not_exists_unique_support_piece`: both pinned charts carry a partition of unity, so a
support point of `V₀ ⊓ V₁` always lies in two distinct pieces.

This file gets the clause a different way, and **without any fibre analysis**.  The leak
locus is closed, and under a universally closed structure morphism its base image is closed
too (`isClosed_image_supportLeak`).  So:

* over the *open complement* of that base image, nothing leaks;
* that complement is a Zariski neighbourhood of every base point it contains, refinable to a
  basic open — the `Localization.Away` shape the pointwise gate consumes.

The leak locus is a genuine obstruction only over its own base image, which is a **closed**
subset of `Spec R`. So the no-leak clause is available on a Zariski-dense open of the base
for free; what a fibre analysis is still needed for is the base points *inside* that closed
image.

## Main declarations

* `AlgebraicGeometry.Scheme.LocalEquations.exists_basicOpen_supportLeak_eq_empty` — a basic
  open around any base point outside the leak's image, over which nothing leaks.
* `Scheme.LocalEquations.forall_fibre_closure_subset_of_supportLeak_inter_eq_empty` —
  leak-freeness over an open of the base gives the assembler's fibrewise clause there.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

/-! ## The idempotent brick

I-0209 predicted the shape of the missing construction: the canonical idempotents of a
finite projective colength algebra split the divisor scheme into packets, and a piece
swallowing a packet has a clopen trace, hence carries the certificate.  The algebraic core
of that is elementary and is recorded here: cutting by an idempotent produces a **direct
summand**, so projectivity is inherited with no flatness or finiteness input. -/

-- Stated in the ROOT namespace: these are statements about modules, not about schemes, so
-- they must not resolve as `AlgebraicGeometry.Module.…`.
end AlgebraicGeometry

section Idempotent

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]

set_option maxHeartbeats 1000000 in
-- The `Ideal`-to-`Submodule` coercion in the quotient makes `liftQ` elaboration expensive.
/-- **Cutting by an idempotent gives a direct summand.** For `e` idempotent, multiplication
by `e` is a well-defined `R`-linear section of `B ↠ B ⧸ (1 - e)`, so the quotient is a
retract of `B` and inherits projectivity.

This is the algebraic core of the packet-splitting construction I-0209 asks for: an
idempotent of the colength algebra cuts out a clopen packet, and the corresponding quotient
is projective for free. -/
theorem Module.Projective.quotient_span_singleton_one_sub_of_isIdempotentElem
    [Module.Projective R B] (e : B) (he : IsIdempotentElem e) :
    Module.Projective R (B ⧸ (Ideal.span {1 - e}).restrictScalars R) := by
  set P := (Ideal.span {1 - e}).restrictScalars R with hP
  set s : (B ⧸ P) →ₗ[R] B :=
    P.liftQ (LinearMap.mulLeft R e) (by
      intro x hx
      have hx' : x ∈ Ideal.span {1 - e} := hx
      rw [Ideal.mem_span_singleton] at hx'
      obtain ⟨c, rfl⟩ := hx'
      change e * ((1 - e) * c) = 0
      rw [← mul_assoc, mul_sub, mul_one, he.eq, sub_self, zero_mul]) with hs
  refine Module.Projective.of_split s P.mkQ (LinearMap.ext fun y => ?_)
  obtain ⟨b, rfl⟩ := P.mkQ_surjective y
  change P.mkQ (e * b) = P.mkQ b
  rw [← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  change e * b - b ∈ Ideal.span {1 - e}
  rw [Ideal.mem_span_singleton]
  exact ⟨-b, by ring⟩

set_option maxHeartbeats 1000000 in
-- Same elaboration cost as the projective companion.
/-- **The flat companion.** A retract of a flat module is flat, so an idempotent cut also
inherits flatness.  This is the form that applies to the DD-R pieces: the piece section
rings `Γ(relCurve C R, pieces j)` are known **flat** over `R` (localizations of the free
pinned-chart rings, `FinCoverData.flat_sections_pieces`) rather than projective, so it is
this version that discharges the (c1) input from a packet idempotent. -/
theorem Module.Flat.quotient_span_singleton_one_sub_of_isIdempotentElem
    [Module.Flat R B] (e : B) (he : IsIdempotentElem e) :
    Module.Flat R (B ⧸ (Ideal.span {1 - e}).restrictScalars R) := by
  set P := (Ideal.span {1 - e}).restrictScalars R with hP
  set s : (B ⧸ P) →ₗ[R] B :=
    P.liftQ (LinearMap.mulLeft R e) (by
      intro x hx
      have hx' : x ∈ Ideal.span {1 - e} := hx
      rw [Ideal.mem_span_singleton] at hx'
      obtain ⟨c, rfl⟩ := hx'
      change e * ((1 - e) * c) = 0
      rw [← mul_assoc, mul_sub, mul_one, he.eq, sub_self, zero_mul]) with hs
  exact Module.Flat.of_retract s P.mkQ (LinearMap.ext fun y => by
    obtain ⟨b, rfl⟩ := P.mkQ_surjective y
    change P.mkQ (e * b) = P.mkQ b
    rw [← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    change e * b - b ∈ Ideal.span {1 - e}
    rw [Ideal.mem_span_singleton]
    exact ⟨-b, by ring⟩)

end Idempotent

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

namespace Scheme.LocalEquations

variable {X : Scheme.{u}} {R : Type u} [CommRing R] (d : X.LocalEquations)

/-- **A leak-free basic open around any base point outside the leak's image.** The leak
locus is closed and its base image is closed under a universally closed morphism, so the
complement is open; refining it to a basic open (`PrimeSpectrum.isTopologicalBasis_basic_opens`)
gives the `Localization.Away` shape the pointwise certificate gate consumes. -/
theorem exists_basicOpen_supportLeak_eq_empty (f : X ⟶ Spec (CommRingCat.of R))
    [UniversallyClosed f] (U : X.Opens) {p : PrimeSpectrum R}
    (hp : (p : Spec (CommRingCat.of R)) ∉ f.base '' d.supportLeak U) :
    ∃ r : R, r ∉ p.asIdeal ∧
      f.base ⁻¹' (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R))
        ∩ d.supportLeak U = ∅ := by
  classical
  have hopen : IsOpen ((f.base '' d.supportLeak U)ᶜ) :=
    (d.isClosed_image_supportLeak f U).isOpen_compl
  obtain ⟨W, hWmem, hpW, hWsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (a := p) hp hopen
  obtain ⟨r, rfl⟩ := hWmem
  refine ⟨r, (PrimeSpectrum.mem_basicOpen r p).mp hpW, ?_⟩
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨hxb, hxl⟩
  exact hWsub hxb ⟨x, hxl, rfl⟩

/-- **Leak-freeness over a base open gives the assembler's fibrewise clause there.** If no
point over the base set `V` leaks out of `U`, then for every base point `s ∈ V` the fibre of
the closure of the *restricted* trace stays in `U`.

This is the bridge from the closed-image mechanism to the shape
`finite_colength_of_forall_fibre_closure_subset` consumes: the closure is taken of the trace
restricted over `V`, which only shrinks it, so a leak would have to be a leak of the
unrestricted trace. -/
theorem forall_fibre_closure_subset_of_supportLeak_inter_eq_empty
    (f : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens) {V : Set (Spec (CommRingCat.of R))}
    (hV : f.base ⁻¹' V ∩ d.supportLeak U = ∅) :
    ∀ s ∈ V, f.base ⁻¹' {s}
        ∩ closure (d.supportLocus ∩ (U : Set X) ∩ f.base ⁻¹' V)
      ⊆ (U : Set X) := by
  intro s hs x hx
  by_contra hxU
  -- `x` is in the closure of the full trace, and outside `U`, hence a leak
  have hcl : x ∈ closure (d.supportLocus ∩ (U : Set X)) :=
    closure_mono Set.inter_subset_left hx.2
  have hxV : x ∈ f.base ⁻¹' V := by
    have : f.base x = s := hx.1
    rw [Set.mem_preimage, this]; exact hs
  exact Set.eq_empty_iff_forall_notMem.mp hV x ⟨hxV, hcl, hxU⟩

/-! ## No-leak IS the Z-clopen condition

The recorded design constraint of this project (memory I-0209, "the Z-clopen certificate
principle") says a piece carries an `R`-finite colength exactly when its trace on the divisor
scheme is *clopen* in that scheme.  The following two lemmas identify that principle with the
leak locus, so the two vocabularies are the same statement:

the piece trace `supp ∩ U` is always **open** in the subspace `supp` (as `U` is open), so it
is clopen there precisely when it is closed in the ambient space — precisely when nothing
leaks. -/

/-- **Leak-freeness is clopen-ness of the trace in the support.** The forward direction of
the identification with the Z-clopen principle (I-0209). -/
theorem isClopen_trace_of_supportLeak_eq_empty (U : X.Opens)
    (h : d.supportLeak U = ∅) :
    IsClopen ((fun x : d.supportLocus => x.val) ⁻¹' (U : Set X)) := by
  have hclosed : IsClosed (d.supportLocus ∩ (U : Set X)) :=
    (d.isClosed_supportLocus_inter_iff_supportLeak_eq_empty U).mpr h
  refine ⟨?_, U.isOpen.preimage continuous_subtype_val⟩
  have heq : (fun x : d.supportLocus => x.val) ⁻¹' (U : Set X)
      = (fun x : d.supportLocus => x.val) ⁻¹' (d.supportLocus ∩ (U : Set X)) := by
    ext x; simp
  rw [heq]
  exact hclosed.preimage continuous_subtype_val

/-- The converse, from the closedness half alone: a trace closed in the support leaks
nothing.  (The openness half is automatic — see `supportLeak_eq_empty_iff_isClosed_trace`
for the honest equivalence.) -/
theorem supportLeak_eq_empty_of_isClopen_trace (U : X.Opens)
    (h : IsClosed ((fun x : d.supportLocus => x.val) ⁻¹' (U : Set X))) :
    d.supportLeak U = ∅ := by
  refine (d.isClosed_supportLocus_inter_iff_supportLeak_eq_empty U).mp ?_
  -- a set closed in the closed subspace `supp` is closed in `X`
  obtain ⟨T, hT, hTeq⟩ := (isClosed_induced_iff (f := fun x : d.supportLocus => x.val)).mp h
  have heq : d.supportLocus ∩ (U : Set X) = d.supportLocus ∩ T := by
    ext x
    constructor
    · rintro ⟨hxs, hxU⟩
      exact ⟨hxs, (Set.ext_iff.mp hTeq ⟨x, hxs⟩).mpr hxU⟩
    · rintro ⟨hxs, hxT⟩
      exact ⟨hxs, (Set.ext_iff.mp hTeq ⟨x, hxs⟩).mp hxT⟩
  rw [heq]
  exact d.isClosed_supportLocus.inter hT

/-- **The honest equivalence.** Leak-freeness at `U` is exactly closedness of the piece
trace in the subspace `supp` — and since that trace is *always* open there (`U` is open), it
is exactly clopen-ness of the trace, i.e. the Z-clopen condition of I-0209.

The `IsClopen` spelling of the forward direction (`isClopen_trace_of_supportLeak_eq_empty`)
carries a free rider: the openness half holds unconditionally, so the content of the
identification is this `Iff` on the closedness half. -/
theorem supportLeak_eq_empty_iff_isClosed_trace (U : X.Opens) :
    d.supportLeak U = ∅ ↔
      IsClosed ((fun x : d.supportLocus => x.val) ⁻¹' (U : Set X)) :=
  ⟨fun h => (d.isClopen_trace_of_supportLeak_eq_empty U h).1,
    d.supportLeak_eq_empty_of_isClopen_trace U⟩

/-- The piece trace is always **open** in the support, with no hypothesis — the half of
clopen-ness that carries no information. -/
theorem isOpen_trace (U : X.Opens) :
    IsOpen ((fun x : d.supportLocus => x.val) ⁻¹' (U : Set X)) :=
  U.isOpen.preimage continuous_subtype_val

end Scheme.LocalEquations

/-! ## The (c1) clause from a clopen trace

Assembling the identification with the landed finiteness engine: a clopen piece trace gives
the assembler's `hnoLeak` at that piece, hence its `Module.Finite` colength.  Combined with
`SupportTube.projective_colength_of_forall_tmul_residueField` this is the whole (c1) input,
so under the Z-clopen hypothesis the certificate's finiteness side needs no fibre analysis.

What remains outstanding for the lane is only the *production* of the clopen trace, i.e.
I-0209's `W`-as-algebra extraction. `PrimeSpectrum.isClopen_iff_zeroLocus` and
`PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen` are the mathlib translations that
turn a clopen packet of the divisor scheme into the idempotent the brick above consumes. -/

section Clopen

variable {k : Type u} [Field k] {C : Over (Spec (.of k))} [IsProper C.hom]
variable {R : Type u} [CommRing R] [Algebra k R]
variable {pi : C.left ⟶ P1 k} [IsFinite pi]
variable {d : (relCurve C R).LocalEquations}

namespace DivisorAdaptation

variable (A : DivisorAdaptation C R pi d)

/-- **A clopen piece trace gives the (c1)-finite clause at that piece.** Reading the
identification `supportLeak = ∅ ↔ clopen trace` into the landed finiteness engine
`finite_colength_of_supportLeak_eq_empty`. -/
theorem finite_colength_of_isClopen_trace (j : A.index)
    (h : IsClosed ((fun x : d.supportLocus => x.val) ⁻¹'
      (A.pieces j : Set (relCurve C R)))) :
    Module.Finite R (A.colength j) :=
  A.finite_colength_of_supportLeak_eq_empty j
    (d.supportLeak_eq_empty_of_isClopen_trace _ h)

/-- **The full (c1) data at a piece with clopen trace.** Finiteness from the clopen trace,
projectivity from fibrewise regularity of the piece equation — which for a seed adaptation
is landed (`ThetaGeneratorSeed.divisorAdaptation_fibre_regular`).  No fibre containment and
no flatness of a Čech cokernel enters. -/
theorem finite_and_projective_colength_of_isClopen_trace [IsNoetherianRing R] (j : A.index)
    (h : IsClosed ((fun x : d.supportLocus => x.val) ⁻¹'
      (A.pieces j : Set (relCurve C R))))
    (hreg : ∀ p : PrimeSpectrum R,
      (A.eqn j ⊗ₜ[R] (1 : p.asIdeal.ResidueField) :
          Γ(relCurve C R, A.pieces j) ⊗[R] p.asIdeal.ResidueField) ∈
        nonZeroDivisors
          (Γ(relCurve C R, A.pieces j) ⊗[R] p.asIdeal.ResidueField)) :
    Module.Finite R (A.colength j) ∧ Module.Projective R (A.colength j) := by
  haveI := A.finite_colength_of_isClopen_trace j h
  exact ⟨‹_›, A.projective_colength_of_forall_tmul_residueField j hreg⟩

end DivisorAdaptation

end Clopen

end AlgebraicGeometry
