import Mathlib.Data.Nat.Basic

/-!
# Families of curves

This module records the logical content of the Stacks Project definitions of
prestable, semistable, and stable families of curves.  The type of geometric
fibres is kept abstract so that these definitions can be used before the full
algebraic-space moduli-stack API is available.

The definitions correspond to Stacks tags 0E6T, 0E6Z, and 0E75.
-/

namespace StacksPart08

universe u v w

/-- The data about a family of curves used by the stability definitions.

`GeometricFiber` indexes the geometric fibres.  The first four fields record
the defining conditions of a family of curves; the remaining fields record the
conditions and invariants used to distinguish prestable, semistable, and stable
families.
-/
structure FamilyOfCurves (GeometricFiber : Type u) where
  isFlat : Prop
  isProper : Prop
  isOfFinitePresentation : Prop
  hasRelativeDimensionAtMostOne : Prop
  atWorstNodalOfRelativeDimensionOne : Prop
  pushforwardStructureSheafUniversallyTrivial : Prop
  genus : GeometricFiber → Nat
  hasRationalTail : GeometricFiber → Prop
  hasRationalBridge : GeometricFiber → Prop

/-- Reindex the geometric fibres of a family along a map of indexing types.

The geometric data of the family (flatness, properness, finite presentation,
and the nodal and connectedness conditions) is unchanged.  The fibrewise
invariants are pulled back along `g`.  This is the abstract form of base
change used by the stability definitions in this file. -/
def FamilyOfCurves.reindex {GeometricFiber : Type u} {J : Type v}
    (f : FamilyOfCurves GeometricFiber) (g : J → GeometricFiber) :
    FamilyOfCurves J where
  isFlat := f.isFlat
  isProper := f.isProper
  isOfFinitePresentation := f.isOfFinitePresentation
  hasRelativeDimensionAtMostOne := f.hasRelativeDimensionAtMostOne
  atWorstNodalOfRelativeDimensionOne := f.atWorstNodalOfRelativeDimensionOne
  pushforwardStructureSheafUniversallyTrivial :=
    f.pushforwardStructureSheafUniversallyTrivial
  genus := fun j => f.genus (g j)
  hasRationalTail := fun j => f.hasRationalTail (g j)
  hasRationalBridge := fun j => f.hasRationalBridge (g j)

@[simp]
theorem FamilyOfCurves.reindex_isFlat {GeometricFiber : Type u}
    {J : Type v} (f : FamilyOfCurves GeometricFiber) (g : J → GeometricFiber) :
    (f.reindex g).isFlat = f.isFlat := rfl

@[simp]
theorem FamilyOfCurves.reindex_isProper {GeometricFiber : Type u}
    {J : Type v} (f : FamilyOfCurves GeometricFiber) (g : J → GeometricFiber) :
    (f.reindex g).isProper = f.isProper := rfl

@[simp]
theorem FamilyOfCurves.reindex_isOfFinitePresentation
    {GeometricFiber : Type u} {J : Type v}
    (f : FamilyOfCurves GeometricFiber) (g : J → GeometricFiber) :
    (f.reindex g).isOfFinitePresentation = f.isOfFinitePresentation := rfl

@[simp]
theorem FamilyOfCurves.reindex_hasRelativeDimensionAtMostOne
    {GeometricFiber : Type u} {J : Type v}
    (f : FamilyOfCurves GeometricFiber) (g : J → GeometricFiber) :
    (f.reindex g).hasRelativeDimensionAtMostOne =
      f.hasRelativeDimensionAtMostOne := rfl

@[simp]
theorem FamilyOfCurves.reindex_atWorstNodalOfRelativeDimensionOne
    {GeometricFiber : Type u} {J : Type v}
    (f : FamilyOfCurves GeometricFiber) (g : J → GeometricFiber) :
    (f.reindex g).atWorstNodalOfRelativeDimensionOne =
      f.atWorstNodalOfRelativeDimensionOne := rfl

@[simp]
theorem FamilyOfCurves.reindex_pushforwardStructureSheafUniversallyTrivial
    {GeometricFiber : Type u} {J : Type v}
    (f : FamilyOfCurves GeometricFiber) (g : J → GeometricFiber) :
    (f.reindex g).pushforwardStructureSheafUniversallyTrivial =
      f.pushforwardStructureSheafUniversallyTrivial := rfl

@[simp]
theorem FamilyOfCurves.reindex_genus {GeometricFiber : Type u} {J : Type v}
    (f : FamilyOfCurves GeometricFiber) (g : J → GeometricFiber) (j : J) :
    (f.reindex g).genus j = f.genus (g j) := rfl

@[simp]
theorem FamilyOfCurves.reindex_hasRationalTail
    {GeometricFiber : Type u} {J : Type v}
    (f : FamilyOfCurves GeometricFiber) (g : J → GeometricFiber) (j : J) :
    (f.reindex g).hasRationalTail j = f.hasRationalTail (g j) := rfl

@[simp]
theorem FamilyOfCurves.reindex_hasRationalBridge
    {GeometricFiber : Type u} {J : Type v}
    (f : FamilyOfCurves GeometricFiber) (g : J → GeometricFiber) (j : J) :
    (f.reindex g).hasRationalBridge j = f.hasRationalBridge (g j) := rfl

/-- Reindexing by the identity leaves a family unchanged. -/
@[simp]
theorem FamilyOfCurves.reindex_id {GeometricFiber : Type u}
    (f : FamilyOfCurves GeometricFiber) : f.reindex id = f := by
  cases f
  rfl

/-- Reindexing successively is the same as reindexing by the composite map. -/
@[simp]
theorem FamilyOfCurves.reindex_comp {GeometricFiber : Type u} {J : Type v}
    {K : Type w} (f : FamilyOfCurves GeometricFiber) (g : J → GeometricFiber)
    (h : K → J) : (f.reindex g).reindex h = f.reindex (g ∘ h) := by
  cases f
  rfl

/-- The four conditions defining a family of curves. -/
def FamilyOfCurves.SatisfiesFamilyConditions {GeometricFiber : Type u}
    (f : FamilyOfCurves GeometricFiber) : Prop :=
  f.isFlat ∧ f.isProper ∧ f.isOfFinitePresentation ∧
    f.hasRelativeDimensionAtMostOne

/-- Reindexing preserves the four ambient conditions of a family of curves. -/
theorem FamilyOfCurves.reindex_satisfiesFamilyConditions
    {GeometricFiber : Type u} {J : Type v}
    (f : FamilyOfCurves GeometricFiber) (g : J → GeometricFiber) :
    (f.reindex g).SatisfiesFamilyConditions ↔
      f.SatisfiesFamilyConditions := by
  simp [FamilyOfCurves.SatisfiesFamilyConditions, FamilyOfCurves.reindex]

/-- A family of curves is prestable when it is at worst nodal of relative
dimension one and the equality `f_* O_X = O_S` holds universally (Stacks tag
0E6T). -/
def Prestable {GeometricFiber : Type u} (f : FamilyOfCurves GeometricFiber) : Prop :=
  f.atWorstNodalOfRelativeDimensionOne ∧
    f.pushforwardStructureSheafUniversallyTrivial

/-- A prestable family is semistable when every geometric fibre has genus at
least one and has no rational tail (Stacks tag 0E6Z). -/
def Semistable {GeometricFiber : Type u} (f : FamilyOfCurves GeometricFiber) : Prop :=
  Prestable f ∧
    ∀ s, 1 ≤ f.genus s ∧ ¬ f.hasRationalTail s

/-- A prestable family is stable when every geometric fibre has genus at least
two and has neither a rational tail nor a rational bridge (Stacks tag 0E75). -/
def Stable {GeometricFiber : Type u} (f : FamilyOfCurves GeometricFiber) : Prop :=
  Prestable f ∧
    ∀ s, 2 ≤ f.genus s ∧
      ¬ f.hasRationalTail s ∧ ¬ f.hasRationalBridge s

theorem prestable_iff {GeometricFiber : Type u} (f : FamilyOfCurves GeometricFiber) :
    Prestable f ↔
      f.atWorstNodalOfRelativeDimensionOne ∧
        f.pushforwardStructureSheafUniversallyTrivial :=
  Iff.rfl

theorem semistable_iff {GeometricFiber : Type u} (f : FamilyOfCurves GeometricFiber) :
    Semistable f ↔
      Prestable f ∧ (∀ s, 1 ≤ f.genus s ∧ ¬ f.hasRationalTail s) :=
  Iff.rfl

theorem stable_iff {GeometricFiber : Type u} (f : FamilyOfCurves GeometricFiber) :
    Stable f ↔
      Prestable f ∧
        ∀ s, 2 ≤ f.genus s ∧
          ¬ f.hasRationalTail s ∧ ¬ f.hasRationalBridge s :=
  Iff.rfl

/-- Every semistable family is prestable. -/
theorem Semistable.prestable {GeometricFiber : Type u}
    {f : FamilyOfCurves GeometricFiber} (hf : Semistable f) : Prestable f :=
  hf.1

/-- Every stable family is prestable. -/
theorem Stable.prestable {GeometricFiber : Type u}
    {f : FamilyOfCurves GeometricFiber} (hf : Stable f) : Prestable f :=
  hf.1

/-- Every stable family is semistable. -/
theorem Stable.semistable {GeometricFiber : Type u}
    {f : FamilyOfCurves GeometricFiber} (hf : Stable f) : Semistable f := by
  refine ⟨hf.prestable, ?_⟩
  intro s
  exact ⟨le_trans (by decide : 1 ≤ 2) (hf.2 s).1, (hf.2 s).2.1⟩

/-- Reindexing preserves prestability. -/
theorem FamilyOfCurves.reindex_prestable {GeometricFiber : Type u} {J : Type v}
    (f : FamilyOfCurves GeometricFiber) (g : J → GeometricFiber)
    (hf : Prestable f) : Prestable (f.reindex g) := by
  simpa [Prestable, FamilyOfCurves.reindex] using hf

/-- Reindexing preserves semistability. -/
theorem FamilyOfCurves.reindex_semistable {GeometricFiber : Type u} {J : Type v}
    (f : FamilyOfCurves GeometricFiber) (g : J → GeometricFiber)
    (hf : Semistable f) : Semistable (f.reindex g) := by
  refine ⟨f.reindex_prestable g hf.1, ?_⟩
  intro j
  simpa [FamilyOfCurves.reindex] using hf.2 (g j)

/-- Reindexing preserves stability. -/
theorem FamilyOfCurves.reindex_stable {GeometricFiber : Type u} {J : Type v}
    (f : FamilyOfCurves GeometricFiber) (g : J → GeometricFiber)
    (hf : Stable f) : Stable (f.reindex g) := by
  refine ⟨f.reindex_prestable g hf.1, ?_⟩
  intro j
  simpa [FamilyOfCurves.reindex] using hf.2 (g j)

/-- Reindexing does not change prestability, in either direction. -/
theorem FamilyOfCurves.reindex_prestable_iff {GeometricFiber : Type u}
    {J : Type v} (f : FamilyOfCurves GeometricFiber) (g : J → GeometricFiber) :
    Prestable (f.reindex g) ↔ Prestable f := by
  simp [Prestable, FamilyOfCurves.reindex]

/-- A surjective reindexing reflects semistability. -/
theorem FamilyOfCurves.reindex_semistable_of_surjective
    {GeometricFiber : Type u} {J : Type v}
    (f : FamilyOfCurves GeometricFiber) (g : J → GeometricFiber)
    (hg : Function.Surjective g) (hf : Semistable (f.reindex g)) :
    Semistable f := by
  refine ⟨?_, ?_⟩
  · exact (f.reindex_prestable_iff g).mp hf.1
  · intro s
    obtain ⟨j, rfl⟩ := hg s
    simpa [FamilyOfCurves.reindex] using hf.2 j

/-- A surjective reindexing reflects stability. -/
theorem FamilyOfCurves.reindex_stable_of_surjective
    {GeometricFiber : Type u} {J : Type v}
    (f : FamilyOfCurves GeometricFiber) (g : J → GeometricFiber)
    (hg : Function.Surjective g) (hf : Stable (f.reindex g)) : Stable f := by
  refine ⟨?_, ?_⟩
  · exact (f.reindex_prestable_iff g).mp hf.1
  · intro s
    obtain ⟨j, rfl⟩ := hg s
    simpa [FamilyOfCurves.reindex] using hf.2 j

/-- Method-style alias for `FamilyOfCurves.reindex_prestable`. -/
theorem Prestable.reindex {GeometricFiber : Type u} {J : Type v}
    {f : FamilyOfCurves GeometricFiber} (hf : Prestable f)
    (g : J → GeometricFiber) : Prestable (f.reindex g) :=
  f.reindex_prestable g hf

/-- Method-style alias for `FamilyOfCurves.reindex_semistable`. -/
theorem Semistable.reindex {GeometricFiber : Type u} {J : Type v}
    {f : FamilyOfCurves GeometricFiber} (hf : Semistable f)
    (g : J → GeometricFiber) : Semistable (f.reindex g) :=
  f.reindex_semistable g hf

/-- Method-style alias for `FamilyOfCurves.reindex_stable`. -/
theorem Stable.reindex {GeometricFiber : Type u} {J : Type v}
    {f : FamilyOfCurves GeometricFiber} (hf : Stable f)
    (g : J → GeometricFiber) : Stable (f.reindex g) :=
  f.reindex_stable g hf

/-- A surjective reindexing preserves semistability in both directions. -/
theorem FamilyOfCurves.reindex_semistable_iff_of_surjective
    {GeometricFiber : Type u} {J : Type v}
    (f : FamilyOfCurves GeometricFiber) (g : J → GeometricFiber)
    (hg : Function.Surjective g) :
    Semistable (f.reindex g) ↔ Semistable f := by
  constructor
  · intro h
    exact f.reindex_semistable_of_surjective g hg h
  · intro h
    exact f.reindex_semistable g h

/-- A surjective reindexing preserves stability in both directions. -/
theorem FamilyOfCurves.reindex_stable_iff_of_surjective
    {GeometricFiber : Type u} {J : Type v}
    (f : FamilyOfCurves GeometricFiber) (g : J → GeometricFiber)
    (hg : Function.Surjective g) :
    Stable (f.reindex g) ↔ Stable f := by
  constructor
  · intro h
    exact f.reindex_stable_of_surjective g hg h
  · intro h
    exact f.reindex_stable g h

end StacksPart08
