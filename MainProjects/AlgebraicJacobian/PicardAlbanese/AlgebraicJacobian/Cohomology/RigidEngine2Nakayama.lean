/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Spectrum.Prime.Module

/-!
# RE-2: Nakayama vanishing-propagation and the openness of the vanishing locus

This file is the module-algebra core of the rigid two-term pushforward engine's **VAN**
(vanishing propagation) and **openness** exports (w4-3 worksheet §2.5(b), §3.3). Both are
Noetherian-free: they consume only `Module.Finite R M`, which the engine supplies through
the coherence brick **COH-1** (`Module.Finite R H¹`, over *any* commutative ring).

The engine's degree-one cohomology `H¹` is the two-lattice-pair carrier
`N ⧸ (range ι₀ ⊔ range ι₁)` (worksheet §1.2); it is an ordinary finite `R`-module once
COH-1 has fired. Everything RE-2 says is therefore a fact about a **general finite
`R`-module `M`** — no schemes, no lattice pair (the D1 module-algebra discipline). The
consumers (RE-3/RE-4 and the datum) instantiate `M := H¹` with the COH-1 instance:

* `subsingleton_of_forall_subsingleton_residueField_tensor` is the pinned
  `subsingleton_h1_of_fibrewise`: fibrewise vanishing `∀ p, Subsingleton (H¹ ⊗ κ(p))`
  propagates to `Subsingleton H¹`;
* `isOpen_setOf_subsingleton_residueField_tensor` is the pinned
  `isOpen_fibrewise_vanishing`: the fibrewise-vanishing locus is open (the strata gift,
  the curve-lite replacement for Kleiman's Serre-openness passage, tex 2298–2306).

## The mathlib kit

The fibre `M ⊗[R] κ(p)` is pinned in the worksheet order (`M` on the left, `κ(p)` the
residue field `p.asIdeal.ResidueField`). Its vanishing is characterised through mathlib's
Nakayama gift `Module.mem_support_iff_nontrivial_residueField_tensorProduct`
(`Mathlib/RingTheory/LocalRing/Module.lean`): for finite `M`,
`p ∈ Supp M ↔ Nontrivial (κ(p) ⊗ M)`, whence `p ∉ Supp M ↔ Subsingleton (M ⊗ κ(p))`
after a `TensorProduct.comm`. Vanishing propagation is then `Module.support_eq_empty_iff`
(`Supp M = ∅ ↔ Subsingleton M`, Noetherian-free), and openness is
`Module.isClosed_support` (`Supp M` closed for finite `M`, since `Supp M = Z(Ann M)`) taken
to the complement.

## Deviation from the pinned contract (concurrency-forced)

The pinned statements (worksheet §1.2, `subsingleton_h1_of_fibrewise` /
`isOpen_fibrewise_vanishing`) name the lattice-pair carrier `H¹`, which lives in the RE-1
file (`RigidEngineLattice*`) owned by a concurrent prover and not yet landed. To stay
green and decoupled, RE-2 delivers the **general finite-module** content verbatim; the
`H¹`-named wrappers are one-liners the assembly brick RE-4 adds once RE-1 has landed. This
is exactly the decoupling the worksheet prescribes ("the engine core is module algebra";
RE-2 "nearly all mathlib").
-/

set_option autoImplicit false

universe u

namespace AlgebraicJacobian.RigidEngine

open scoped TensorProduct

variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]

/-- **The fibre criterion (Nakayama).** For a finite `R`-module `M` and a prime `p`, the
residue-field fibre `M ⊗ κ(p)` (worksheet order: `M` on the left, `κ(p) :=
p.asIdeal.ResidueField`) is subsingleton exactly when `p` lies off the support of `M`.

This is mathlib's `Module.mem_support_iff_nontrivial_residueField_tensorProduct` — the
Nakayama step `Mₚ = 0 ↔ M ⊗ κ(p) = 0` for finite `M` — reflected across `not`, with a
`TensorProduct.comm` reconciling the fibre order. 


 * Provenance: CUSTOM.
-/
theorem subsingleton_residueField_tensor_iff_notMem_support [Module.Finite R M]
    (p : PrimeSpectrum R) :
    Subsingleton (M ⊗[R] p.asIdeal.ResidueField) ↔ p ∉ Module.support R M := by
  rw [(TensorProduct.comm R M p.asIdeal.ResidueField).toEquiv.subsingleton_congr,
    ← not_nontrivial_iff_subsingleton,
    ← Module.mem_support_iff_nontrivial_residueField_tensorProduct]

/-- **VAN — vanishing propagation (the pinned `subsingleton_h1_of_fibrewise`).** If every
residue-field fibre `M ⊗ κ(p)` of a finite `R`-module `M` is subsingleton, then `M` itself
is subsingleton. Noetherian-free: consumes only `Module.Finite R M` (the engine's COH-1).

Applied with `M := H¹`, this is the vanishing-propagation clause of Kleiman 3.10 (v)⟹(i):
fibrewise vanishing of `H¹` forces `H¹(C_R, L) = 0` over the whole base. 


 * Provenance: ADAPTED.
-/
theorem subsingleton_of_forall_subsingleton_residueField_tensor [Module.Finite R M]
    (hfib : ∀ p : PrimeSpectrum R, Subsingleton (M ⊗[R] p.asIdeal.ResidueField)) :
    Subsingleton M := by
  rw [← Module.support_eq_empty_iff (R := R), Set.eq_empty_iff_forall_notMem]
  exact fun p ↦ (subsingleton_residueField_tensor_iff_notMem_support p).mp (hfib p)

/-- **The vanishing locus as a complement of the support.** The set of primes at which the
fibre `M ⊗ κ(p)` vanishes is exactly the complement of `Supp M`. 


 * Provenance: CUSTOM.
-/
theorem setOf_subsingleton_residueField_tensor_eq_compl_support [Module.Finite R M] :
    {p : PrimeSpectrum R | Subsingleton (M ⊗[R] p.asIdeal.ResidueField)} =
      (Module.support R M)ᶜ := by
  ext p
  simpa only [Set.mem_setOf_eq, Set.mem_compl_iff] using
    subsingleton_residueField_tensor_iff_notMem_support p

/-- **Openness of the vanishing locus (the pinned `isOpen_fibrewise_vanishing`).** For a
finite `R`-module `M`, the fibrewise-vanishing locus `{p | Subsingleton (M ⊗ κ(p))}` is
open in `Spec R`, being the complement of the closed support `Supp M = Z(Ann M)`.

Applied with `M := H¹`, this is the strata gift (worksheet §3.3): the fibrewise-`H¹`-
vanishing locus is open, the curve-lite replacement for Kleiman's Serre-openness passage
(tex 2298–2306). Noetherian-free. 


 * Provenance: ADAPTED.
-/
theorem isOpen_setOf_subsingleton_residueField_tensor [Module.Finite R M] :
    IsOpen {p : PrimeSpectrum R | Subsingleton (M ⊗[R] p.asIdeal.ResidueField)} := by
  rw [setOf_subsingleton_residueField_tensor_eq_compl_support]
  exact (Module.isClosed_support (R := R) (M := M)).isOpen_compl

/-- **VAN via localizations (auxiliary form).** If every localization `Mₚ` of an
`R`-module `M` vanishes, then `M` is subsingleton. This is `Module.support_eq_empty_iff`
unpacked; unlike the fibre form it needs neither `Module.Finite` nor Nakayama (the support
is defined by the `Mₚ`). Provided for consumers already phrasing vanishing at localizations
rather than at residue fields. 


 * Provenance: CUSTOM.
-/
theorem subsingleton_of_forall_subsingleton_localizedModule
    (hfib : ∀ p : PrimeSpectrum R, Subsingleton (LocalizedModule p.asIdeal.primeCompl M)) :
    Subsingleton M := by
  rw [← Module.support_eq_empty_iff (R := R), Set.eq_empty_iff_forall_notMem]
  exact fun p ↦ Module.notMem_support_iff.mpr (hfib p)

end AlgebraicJacobian.RigidEngine
