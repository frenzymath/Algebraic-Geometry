import StacksPart01Lib.Topology
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Basic opens in the spectrum

The Stacks Project's Zariski-topology chapter denotes the complement of the
vanishing locus of an element by `D(f)`.  Mathlib packages this open subset as
`PrimeSpectrum.basicOpen f`; this file records the basic identities used in
that description.
-/

namespace StacksPart01

open Set Topology

/-- The spectrum is nonempty exactly when the ring is nontrivial. -/
theorem spectrum_nonempty_iff_nontrivial {R : Type*} [CommSemiring R] :
    Nonempty (PrimeSpectrum R) ↔ Nontrivial R := by
  exact PrimeSpectrum.nonempty_iff_nontrivial

/-- The spectrum is empty exactly for a subsingleton ring. -/
theorem spectrum_isEmpty_iff_subsingleton {R : Type*} [CommSemiring R] :
    IsEmpty (PrimeSpectrum R) ↔ Subsingleton R := by
  exact PrimeSpectrum.isEmpty_iff_subsingleton

/-- A basic open is empty exactly when its defining element is nilpotent. -/
theorem standardOpen_eq_bot_iff_isNilpotent {R : Type*} [CommSemiring R] (f : R) :
    PrimeSpectrum.basicOpen f = ⊥ ↔ IsNilpotent f := by
  exact PrimeSpectrum.basicOpen_eq_bot_iff f

/-- Membership in the standard open `D(f)` means that `f` is not in the prime
ideal represented by the point (Stacks, Tag 00E1). -/
theorem mem_standardOpen_iff {R : Type*} [CommSemiring R]
    (f : R) (x : PrimeSpectrum R) :
    x ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ↔
      f ∉ x.asIdeal := by
  exact PrimeSpectrum.mem_basicOpen f x

/-- The standard open of a product is the intersection of the standard opens
(Stacks, Tag 00E0, part (14)). -/
theorem standardOpen_mul {R : Type*} [CommSemiring R] (f g : R) :
    PrimeSpectrum.basicOpen (f * g) =
      PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen g := by
  exact PrimeSpectrum.basicOpen_mul f g

/-- `D(1)` is the whole spectrum. -/
theorem standardOpen_one {R : Type*} [CommSemiring R] :
    PrimeSpectrum.basicOpen (1 : R) = ⊤ := by
  exact PrimeSpectrum.basicOpen_one

/-- `D(0)` is empty. -/
theorem standardOpen_zero {R : Type*} [CommSemiring R] :
    PrimeSpectrum.basicOpen (0 : R) = ⊥ := by
  exact PrimeSpectrum.basicOpen_zero

/-- Standard opens are open in the Zariski topology. -/
theorem isOpen_standardOpen {R : Type*} [CommSemiring R] (f : R) :
    IsOpen (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
  exact PrimeSpectrum.isOpen_basicOpen

/-- The map on spectra induced by a ring homomorphism is continuous
(Stacks, Tag 00E2). -/
theorem continuous_spectrum_comap {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) : Continuous (PrimeSpectrum.comap f) := by
  exact PrimeSpectrum.continuous_comap f

/-- Pullback on spectra respects composition of ring homomorphisms. -/
theorem spectrum_comap_comp {R S T : Type*} [CommSemiring R] [CommSemiring S]
    [CommSemiring T] (f : R →+* S) (g : S →+* T) :
    PrimeSpectrum.comap (g.comp f) =
      (PrimeSpectrum.comap f).comp (PrimeSpectrum.comap g) := by
  exact PrimeSpectrum.comap_comp f g

/-- Pointwise form of `spectrum_comap_comp`. -/
theorem spectrum_comap_comp_apply {R S T : Type*} [CommSemiring R] [CommSemiring S]
    [CommSemiring T] (f : R →+* S) (g : S →+* T) (x : PrimeSpectrum T) :
    PrimeSpectrum.comap (g.comp f) x =
      PrimeSpectrum.comap f (PrimeSpectrum.comap g x) := by
  exact PrimeSpectrum.comap_comp_apply f g x

/-- Pulling a standard open back along `Spec(f)` gives the standard open of
the image of its defining element (Stacks, Tag 00E2). -/
theorem spectrum_comap_preimage_standardOpen {R S : Type*}
    [CommSemiring R] [CommSemiring S] (f : R →+* S) (x : R) :
    (PrimeSpectrum.comap f) ⁻¹' (PrimeSpectrum.basicOpen x : Set (PrimeSpectrum R)) =
      (PrimeSpectrum.basicOpen (f x) : Set (PrimeSpectrum S)) := by
  have h := PrimeSpectrum.comap_basicOpen f x
  have h' := congrArg
    (fun U : TopologicalSpace.Opens (PrimeSpectrum S) => (U : Set (PrimeSpectrum S))) h
  simpa only [TopologicalSpace.Opens.coe_comap, ContinuousMap.coe_mk] using h'

/-- The inverse image of a zero locus under `Spec(f)` is the zero locus of the
image of its defining set. -/
theorem spectrum_comap_preimage_zeroLocus {R S : Type*}
    [CommSemiring R] [CommSemiring S] (f : R →+* S) (s : Set R) :
    (PrimeSpectrum.comap f) ⁻¹' PrimeSpectrum.zeroLocus s =
      PrimeSpectrum.zeroLocus (f '' s) := by
  exact PrimeSpectrum.preimage_comap_zeroLocus f s

/-- The spectrum is quasi-compact (Stacks, Tag 00E8). -/
theorem spectrum_quasiCompact {R : Type*} [CommSemiring R] :
    QuasiCompactSpace (PrimeSpectrum R) := by
  exact isCompact_univ

/-- Every standard open is quasi-compact. -/
theorem standardOpen_quasiCompact {R : Type*} [CommSemiring R] (f : R) :
    IsQuasiCompact (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
  exact PrimeSpectrum.isCompact_basicOpen f

/-- The spectrum of a localization away from `f` is the standard open `D(f)`
(Stacks, Tag 00E4). -/
noncomputable def standardOpen_homeomorph {R : Type*} [CommSemiring R] (f : R) :
    PrimeSpectrum (Localization.Away f) ≃ₜ
      (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
  let h := PrimeSpectrum.localization_away_isOpenEmbedding (Localization.Away f) f
  exact h.isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr
      (PrimeSpectrum.localization_away_comap_range (Localization.Away f) f))

/-- The spectrum of a quotient is homeomorphic to the corresponding closed
zero locus (Stacks, Tag 00E5). -/
noncomputable def spec_quotient_homeomorph {R : Type*} [CommRing R] (I : Ideal R) :
    PrimeSpectrum (R ⧸ I) ≃ₜ
      (PrimeSpectrum.zeroLocus (I : Set R)) := by
  let q : R →+* R ⧸ I := Ideal.Quotient.mk I
  have hmem : ∀ p : PrimeSpectrum (R ⧸ I),
      PrimeSpectrum.comap q p ∈ PrimeSpectrum.zeroLocus (I : Set R) := by
    intro p
    rw [PrimeSpectrum.mem_zeroLocus, PrimeSpectrum.comap_asIdeal]
    intro x hx
    change q x ∈ p.asIdeal
    have hzero' : (Ideal.Quotient.mk I) x = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hx
    have hzero : q x = 0 := by simpa [q] using hzero'
    rw [hzero]
    exact p.asIdeal.zero_mem
  let g := Set.codRestrict (PrimeSpectrum.comap q)
      (PrimeSpectrum.zeroLocus (I : Set R)) hmem
  have hEmb : IsEmbedding g := by
    exact (PrimeSpectrum.isClosedEmbedding_comap_of_surjective
      (R := R) (S := R ⧸ I) q Ideal.Quotient.mk_surjective).isEmbedding.codRestrict
      _ hmem
  have hsurj : Function.Surjective g := by
    intro z
    let e := Ideal.primeSpectrumQuotientOrderIsoZeroLocus I
    obtain ⟨p, hp⟩ := e.surjective z
    refine ⟨p, ?_⟩
    apply Subtype.ext
    dsimp [g]
    exact congrArg Subtype.val hp
  exact hEmb.toHomeomorphOfSurjective hsurj

end StacksPart01
