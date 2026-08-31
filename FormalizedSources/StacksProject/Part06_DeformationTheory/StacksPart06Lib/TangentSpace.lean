import StacksPart06Lib.TrivialSquareZero

/-!
# Tangent-space evaluation

For a set-valued test functor, the tangent space is its value on the dual
numbers.  The definitions here isolate that evaluation from the additional
categorical hypotheses used by the full deformation theory.
-/

namespace StacksPart06Lib

universe u v

section

variable (R : Type u) [CommRing R]

/-- The dual-number test object used to evaluate tangent spaces. -/
abbrev tangentTestObject := DualNumbers R

/-- The tangent space of a set-valued test functor on test-object types.

The categorical structure on the test objects is introduced by the later
deformation-theory modules; this foundational definition only records the
evaluation at the dual numbers.
-/
def tangentSpace (F : Type u → Type v) : Type v :=
  F (tangentTestObject R)

omit [CommRing R] in
@[simp]
theorem tangentSpace_def (F : Type u → Type v) :
    tangentSpace R F = F (tangentTestObject R) :=
  rfl

/-- Evaluation of a natural transformation on the tangent test object. -/
def tangentMap {F G : Type u → Type v}
    (η : ∀ A : Type u, F A → G A) : tangentSpace R F → tangentSpace R G :=
  η (tangentTestObject R)

omit [CommRing R] in
@[simp]
theorem tangentMap_apply {F G : Type u → Type v}
    (η : ∀ A : Type u, F A → G A) (x : tangentSpace R F) :
    tangentMap R η x = η (tangentTestObject R) x :=
  rfl

omit [CommRing R] in
theorem tangentMap_id {F : Type u → Type v} :
    tangentMap R (F := F) (G := F) (fun _ x => x) =
      (id : tangentSpace R F → tangentSpace R F) := by
  rfl

omit [CommRing R] in
theorem tangentMap_comp {F G H : Type u → Type v}
    (η : ∀ A : Type u, F A → G A) (θ : ∀ A : Type u, G A → H A) :
    tangentMap R (F := F) (G := H) (fun A x => θ A (η A x)) =
      (tangentMap R θ) ∘ (tangentMap R η) := by
  rfl

end

end StacksPart06Lib
