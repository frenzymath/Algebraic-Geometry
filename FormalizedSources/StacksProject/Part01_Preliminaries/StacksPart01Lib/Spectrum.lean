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

/-- Every nontrivial ring has a maximal ideal (Stacks, Tag 00E0). -/
theorem maximal_ideal_exists {R : Type*} [CommSemiring R] [Nontrivial R] :
    ∃ M : Ideal R, M.IsMaximal := by
  exact Ideal.exists_maximal R

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

/-- The spectrum of a localization is homeomorphic to the subspace of prime
ideals disjoint from the localized submonoid (Stacks, Tag 00E3). -/
noncomputable def spec_localization_homeomorph
    {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] :
    PrimeSpectrum S ≃ₜ
      {p : PrimeSpectrum R // Disjoint (M : Set R) p.asIdeal} := by
  let h := PrimeSpectrum.localization_comap_isEmbedding S M
  exact h.toHomeomorph.trans
    (Homeomorph.setCongr (PrimeSpectrum.localization_comap_range S M))

/-- Under `spec_localization_homeomorph`, a prime is sent to its inverse image
along the localization map. -/
@[simp]
theorem spec_localization_homeomorph_apply
    {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (p : PrimeSpectrum S) :
    (spec_localization_homeomorph M p : PrimeSpectrum R) =
      PrimeSpectrum.comap (algebraMap R S) p := by
  rfl

/-- The spectrum of a localization away from `f` is the standard open `D(f)`
(Stacks, Tag 00E4). -/
noncomputable def standardOpen_homeomorph {R : Type*} [CommSemiring R] (f : R) :
    PrimeSpectrum (Localization.Away f) ≃ₜ
      (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
  let h := PrimeSpectrum.localization_away_isOpenEmbedding (Localization.Away f) f
  exact h.isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr
      (PrimeSpectrum.localization_away_comap_range (Localization.Away f) f))

/-- Under the standard-open homeomorphism, a prime is sent to its inverse
image along the localization map (Stacks, Tag 00E4). -/
@[simp]
theorem standardOpen_homeomorph_apply
    {R : Type*} [CommSemiring R] (f : R)
    (p : PrimeSpectrum (Localization.Away f)) :
    (standardOpen_homeomorph f p : PrimeSpectrum R) =
      PrimeSpectrum.comap (algebraMap R (Localization.Away f)) p := by
  rfl

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

/-! ### Further affine-spectrum topological interfaces -/

/-- The spectrum of a product is the disjoint union of the two spectra
(Stacks, Tag 00ED). -/
noncomputable def spec_product_homeomorph
    {R S : Type*} [CommSemiring R] [CommSemiring S] :
    (PrimeSpectrum R ⊕ PrimeSpectrum S) ≃ₜ PrimeSpectrum (R × S) :=
  PrimeSpectrum.primeSpectrumProdHomeo.symm

/-- The left component of the product-spectrum homeomorphism is induced by
the first projection (Stacks, Tag 00ED). -/
@[simp]
theorem spec_product_homeomorph_inl
    {R S : Type*} [CommSemiring R] [CommSemiring S]
    (p : PrimeSpectrum R) :
    spec_product_homeomorph (R := R) (S := S) (Sum.inl p) =
      PrimeSpectrum.comap (RingHom.fst R S) p := by
  exact PrimeSpectrum.primeSpectrumProd_symm_inl p

/-- The right component of the product-spectrum homeomorphism is induced by
the second projection (Stacks, Tag 00ED). -/
@[simp]
theorem spec_product_homeomorph_inr
    {R S : Type*} [CommSemiring R] [CommSemiring S]
    (p : PrimeSpectrum S) :
    spec_product_homeomorph (R := R) (S := S) (Sum.inr p) =
      PrimeSpectrum.comap (RingHom.snd R S) p := by
  exact PrimeSpectrum.primeSpectrumProd_symm_inr p

/-- Closed subsets of an affine spectrum are precisely zero loci of ideals
(Stacks, Tag 00E0). -/
theorem isClosed_iff_zeroLocus_ideal {R : Type*} [CommSemiring R]
    (Z : Set (PrimeSpectrum R)) :
    IsClosed Z ↔ ∃ I : Ideal R, Z = PrimeSpectrum.zeroLocus (I : Set R) := by
  exact PrimeSpectrum.isClosed_iff_zeroLocus_ideal Z

/-- Every zero locus in an affine spectrum is closed. -/
theorem isClosed_zeroLocus {R : Type*} [CommSemiring R] (s : Set R) :
    IsClosed (PrimeSpectrum.zeroLocus s) := by
  exact PrimeSpectrum.isClosed_zeroLocus s

/-! ### Functorial closed loci and specialization -/

/-- A surjective ring map induces a closed embedding on affine spectra
(Stacks, Tag 00E5). -/
theorem spectrum_comap_isClosedEmbedding_of_surjective
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) :
    IsClosedEmbedding (PrimeSpectrum.comap f) := by
  exact PrimeSpectrum.isClosedEmbedding_comap_of_surjective S f hf

/-- The image of the spectrum map of a surjection is the zero locus of its
kernel (Stacks, Tag 00E5). -/
theorem spectrum_comap_range_of_surjective
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) :
    Set.range (PrimeSpectrum.comap f) =
      PrimeSpectrum.zeroLocus (RingHom.ker f : Set R) := by
  exact range_comap_of_surjective S f hf

/-- A surjective spectrum map transports closed loci by ideal comap. -/
theorem spectrum_comap_image_zeroLocus_of_surjective
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (I : Ideal S) :
    PrimeSpectrum.comap f '' PrimeSpectrum.zeroLocus (I : Set S) =
      PrimeSpectrum.zeroLocus (Ideal.comap f I : Set R) := by
  exact image_comap_zeroLocus_eq_zeroLocus_comap S f hf I

/-- Inclusion of affine zero loci is characterized by radical containment. -/
theorem spectrum_zeroLocus_subset_iff_radical_le
    {R : Type*} [CommSemiring R] (I J : Ideal R) :
    PrimeSpectrum.zeroLocus (I : Set R) ⊆
        PrimeSpectrum.zeroLocus (J : Set R) ↔ J ≤ I.radical := by
  exact PrimeSpectrum.zeroLocus_subset_zeroLocus_iff I J

/-- The spectrum map is dense exactly when its kernel is contained in the
nilradical. -/
theorem spectrum_comap_denseRange_iff_ker_le_nilradical
    {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S) :
    DenseRange (PrimeSpectrum.comap f) ↔
      RingHom.ker f ≤ nilradical R := by
  exact PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical f

/-- The closure of a subset of an affine spectrum is the zero locus of its
vanishing ideal. -/
theorem spectrum_zeroLocus_vanishingIdeal_eq_closure
    {R : Type*} [CommSemiring R] (t : Set (PrimeSpectrum R)) :
    PrimeSpectrum.zeroLocus (PrimeSpectrum.vanishingIdeal t : Set R) =
      closure t := by
  exact PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure t

/-- A clopen subset of an affine spectrum is a unique idempotent standard open
(Stacks, Tag 00EE). -/
theorem existsUnique_idempotent_basicOpen_eq_of_isClopen
    {R : Type*} [CommRing R] {U : Set (PrimeSpectrum R)}
    (hU : IsClopen U) :
    ∃! e : R, IsIdempotentElem e ∧
      U = (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R)) := by
  exact PrimeSpectrum.existsUnique_idempotent_basicOpen_eq_of_isClopen hU

/-- A point outside a closed zero locus has a standard-open neighbourhood
disjoint from that zero locus (Stacks, Tag 00E0). -/
theorem exists_standardOpen_disjoint_zeroLocus {R : Type*} [CommSemiring R]
    {I : Ideal R} {p : PrimeSpectrum R}
    (hp : p ∉ PrimeSpectrum.zeroLocus (I : Set R)) :
    ∃ f : R, f ∈ I ∧ f ∉ p.asIdeal ∧
      Disjoint (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R))
        (PrimeSpectrum.zeroLocus (I : Set R)) := by
  have hnot : ¬ (I : Set R) ⊆ p.asIdeal := by
    simpa only [PrimeSpectrum.mem_zeroLocus] using hp
  obtain ⟨f, hfI, hfp⟩ := Set.not_subset.mp hnot
  refine ⟨f, hfI, hfp, ?_⟩
  rw [Set.disjoint_left]
  intro q hqopen hqzero
  have hqnot : f ∉ q.asIdeal := (PrimeSpectrum.mem_basicOpen f q).mp hqopen
  have hqI : f ∈ q.asIdeal :=
    (PrimeSpectrum.mem_zeroLocus q (I : Set R)).mp hqzero hfI
  exact hqnot hqI

end StacksPart01
