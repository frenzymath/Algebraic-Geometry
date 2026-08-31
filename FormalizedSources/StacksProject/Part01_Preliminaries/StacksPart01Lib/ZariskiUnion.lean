import StacksPart01Lib.Zariski

/-!
# Arbitrary unions of standard opens

This is the set-theoretic union statement in the Stacks Project's Zariski
topology lemma (Tag 00E0, part (16)).
-/

namespace StacksPart01

open Set

namespace Zariski

/-- The union of a family of standard opens is the complement of its common
zero locus (Stacks, Tag 00E0, part (16)). -/
theorem standardOpen_iUnion_eq_compl_zeroLocus_range {R : Type*} [CommSemiring R]
    {ι : Type*} (f : ι → R) :
    (⋃ i, (PrimeSpectrum.basicOpen (f i) : Set (PrimeSpectrum R))) =
      (PrimeSpectrum.zeroLocus (Set.range f))ᶜ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_compl_iff, PrimeSpectrum.mem_zeroLocus]
  constructor
  · rintro ⟨i, hi⟩ hsub
    exact hi (hsub ⟨i, rfl⟩)
  · intro hnot
    by_contra hno
    apply hnot
    intro y hy
    rcases hy with ⟨i, rfl⟩
    by_contra hi
    exact hno ⟨i, hi⟩

end Zariski

end StacksPart01
