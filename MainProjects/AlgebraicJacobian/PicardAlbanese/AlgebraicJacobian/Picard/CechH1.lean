/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.CategoryTheory.Sites.NonabelianCohomology.H1
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.Category.Preorder
import AlgebraicJacobian.Picard.UnitsPresheaf

/-!
# Čech 1-cocycles: restriction, poset pair data, and commutative group structure

This file extends Mathlib's fixed-family nonabelian Čech layer
(`CategoryTheory.PresheafOfGroups.OneCocycle`, `H1`) with the three pieces of
infrastructure needed for a Čech-style Picard group (all stated generically; this file
is a Mathlib-PR candidate and contains no algebraic geometry):

1. **Restriction along an indexwise refinement.** For families `U V : I → C` and maps
   `f : ∀ i, V i ⟶ U i`, cochains/cocycles/`H1`-classes restrict along `f`, strictly
   functorially (`res_res` holds on the nose at the cochain level).
2. **The poset bridge.** Over a poset with binary infima, a 1-cochain is determined by
   its values `evInf i j` at the infima `U i ⊓ U j` (`ev_eq_evInf`), and a 1-cocycle can
   be built from classical pair data satisfying the cocycle condition at triple infima
   (`OneCocycle.ofPairs`). Consumers never need to touch `ev` directly.
3. **Commutative group structure.** When the presheaf takes values in `CommGrpCat`,
   1-cocycles form a commutative group under pointwise multiplication (the cocycle
   condition for products needs commutativity) and this descends to `H1`; restriction
   is then a group homomorphism (`H1.resHom`).

## Main declarations

* `CategoryTheory.PresheafOfGroups.OneCochain.res`, `OneCocycle.res`, `H1.res`:
  restriction along an indexwise refinement, with `res_res` and `res_id`.
* `CategoryTheory.PresheafOfGroups.OneCochain.evInf`, `ev_eq_evInf`: over a poset with
  binary infima, evaluation of a cochain at `U i ⊓ U j` determines it.
* `CategoryTheory.PresheafOfGroups.OneCocycle.ofPairs`: the classical construction of a
  cocycle from pair data `g i j` on binary infima with the triple-infimum condition.
* `CategoryTheory.PresheafOfGroups.OneCocycle.isCohomologous_iff_evInf`: the coboundary
  relation in classical pair form.
* `CategoryTheory.PresheafOfGroups.H1.subsingleton_of_forall_le`: if the members of the
  family are mutually comparable (e.g. all equal to a top element), `H1` is trivial.
* `CommGroup (OneCocycle (G ⋙ forget₂ CommGrpCat GrpCat) U)` and
  `CommGroup (H1 (G ⋙ forget₂ CommGrpCat GrpCat) U)` for `G : Cᵒᵖ ⥤ CommGrpCat`.
* `CategoryTheory.PresheafOfGroups.H1.resHom`: restriction as a group homomorphism.
-/

set_option autoImplicit false

universe w' w v u

open CategoryTheory Opposite

namespace CategoryTheory.PresheafOfGroups

variable {C : Type u} [Category.{v} C] {I : Type w'}

/-! ## Restriction along an indexwise refinement -/

section Res

variable {G : Cᵒᵖ ⥤ GrpCat.{w}} {U V W : I → C}

namespace OneCochain

/-- Restriction of a 1-cochain along an indexwise refinement `f : ∀ i, V i ⟶ U i`. -/
def res (γ : OneCochain G U) (f : ∀ i, V i ⟶ U i) : OneCochain G V where
  ev i j _ a b := γ.ev i j (a ≫ f i) (b ≫ f j)
  ev_precomp i j T T' φ a b := by simp

@[simp]
lemma res_ev (γ : OneCochain G U) (f : ∀ i, V i ⟶ U i) (i j : I) {T : C}
    (a : T ⟶ V i) (b : T ⟶ V j) :
    (γ.res f).ev i j a b = γ.ev i j (a ≫ f i) (b ≫ f j) :=
  rfl

@[simp]
lemma one_res (f : ∀ i, V i ⟶ U i) : (1 : OneCochain G U).res f = 1 :=
  rfl

@[simp]
lemma mul_res (γ₁ γ₂ : OneCochain G U) (f : ∀ i, V i ⟶ U i) :
    (γ₁ * γ₂).res f = γ₁.res f * γ₂.res f :=
  rfl

@[simp]
lemma inv_res (γ : OneCochain G U) (f : ∀ i, V i ⟶ U i) :
    (γ⁻¹).res f = (γ.res f)⁻¹ :=
  rfl

/-- Restriction is strictly functorial at the cochain level. -/
@[simp]
lemma res_res (γ : OneCochain G U) (f : ∀ i, V i ⟶ U i) (g : ∀ i, W i ⟶ V i) :
    (γ.res f).res g = γ.res (fun i ↦ g i ≫ f i) := by
  ext i j T a b
  simp

@[simp]
lemma res_id (γ : OneCochain G U) : γ.res (fun i ↦ 𝟙 (U i)) = γ := by
  ext i j T a b
  simp

end OneCochain

namespace OneCocycle

lemma toOneCochain_injective :
    Function.Injective (toOneCochain : OneCocycle G U → OneCochain G U) := by
  rintro ⟨γ₁, h₁⟩ ⟨γ₂, h₂⟩ h
  simpa using h

@[ext]
lemma ext {γ₁ γ₂ : OneCocycle G U} (h : γ₁.toOneCochain = γ₂.toOneCochain) : γ₁ = γ₂ :=
  toOneCochain_injective h

/-- Restriction of a 1-cocycle along an indexwise refinement `f : ∀ i, V i ⟶ U i`. -/
def res (γ : OneCocycle G U) (f : ∀ i, V i ⟶ U i) : OneCocycle G V where
  toOneCochain := γ.toOneCochain.res f
  ev_trans i j k T a b c := by
    simp only [OneCochain.res_ev]
    exact γ.ev_trans i j k (a ≫ f i) (b ≫ f j) (c ≫ f k)

@[simp]
lemma res_toOneCochain (γ : OneCocycle G U) (f : ∀ i, V i ⟶ U i) :
    (γ.res f).toOneCochain = γ.toOneCochain.res f :=
  rfl

@[simp]
lemma res_ev (γ : OneCocycle G U) (f : ∀ i, V i ⟶ U i) (i j : I) {T : C}
    (a : T ⟶ V i) (b : T ⟶ V j) :
    (γ.res f).ev i j a b = γ.ev i j (a ≫ f i) (b ≫ f j) :=
  rfl

@[simp]
lemma one_res (f : ∀ i, V i ⟶ U i) : (1 : OneCocycle G U).res f = 1 :=
  rfl

@[simp]
lemma res_res (γ : OneCocycle G U) (f : ∀ i, V i ⟶ U i) (g : ∀ i, W i ⟶ V i) :
    (γ.res f).res g = γ.res (fun i ↦ g i ≫ f i) :=
  ext (γ.toOneCochain.res_res f g)

@[simp]
lemma res_id (γ : OneCocycle G U) : γ.res (fun i ↦ 𝟙 (U i)) = γ :=
  ext γ.toOneCochain.res_id

end OneCocycle

lemma OneCohomologyRelation.res {γ₁ γ₂ : OneCochain G U} {α : ZeroCochain G U}
    (h : OneCohomologyRelation γ₁ γ₂ α) (f : ∀ i, V i ⟶ U i) :
    OneCohomologyRelation (γ₁.res f) (γ₂.res f) (fun i ↦ G.map (f i).op (α i)) := by
  intro i j T a b
  simpa [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    using h i j (a ≫ f i) (b ≫ f j)

lemma OneCocycle.IsCohomologous.res {γ₁ γ₂ : OneCocycle G U} (h : γ₁.IsCohomologous γ₂)
    (f : ∀ i, V i ⟶ U i) : (γ₁.res f).IsCohomologous (γ₂.res f) := by
  obtain ⟨α, hα⟩ := h
  exact ⟨_, hα.res f⟩

/-- Restriction of degree-one cohomology classes along an indexwise refinement. -/
def H1.res (f : ∀ i, V i ⟶ U i) : H1 G U → H1 G V :=
  Quot.map (·.res f) (fun _ _ h ↦ h.res f)

@[simp]
lemma H1.res_class (f : ∀ i, V i ⟶ U i) (γ : OneCocycle G U) :
    H1.res f γ.class = (γ.res f).class :=
  rfl

/-- Restriction of `H1` classes is strictly functorial. -/
lemma H1.res_res (f : ∀ i, V i ⟶ U i) (g : ∀ i, W i ⟶ V i) (x : H1 G U) :
    H1.res g (H1.res f x) = H1.res (fun i ↦ g i ≫ f i) x := by
  induction x using Quot.ind with
  | _ γ => exact congrArg (Quot.mk _) (γ.res_res f g)

@[simp]
lemma H1.res_id (x : H1 G U) : H1.res (fun i ↦ 𝟙 (U i)) x = x := by
  induction x using Quot.ind with
  | _ γ => exact congrArg (Quot.mk _) γ.res_id

@[simp]
lemma H1.res_one (f : ∀ i, V i ⟶ U i) : H1.res f (1 : H1 G U) = 1 :=
  rfl

end Res

/-! ## The poset bridge: pair data on binary infima -/

section Poset

variable {P : Type u} [SemilatticeInf P] {G : Pᵒᵖ ⥤ GrpCat.{w}} {U : I → P}

private lemma map_map (G : Pᵒᵖ ⥤ GrpCat.{w}) {a b c : P} (h₁ : a ≤ b) (h₂ : b ≤ c)
    (x : G.obj (op c)) :
    G.map (homOfLE h₁).op (G.map (homOfLE h₂).op x) = G.map (homOfLE (h₁.trans h₂)).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]

namespace OneCochain

/-- The value of a 1-cochain on the binary infimum `U i ⊓ U j`. Over a poset with binary
infima this determines the whole cochain, see `ev_eq_evInf`. -/
def evInf (γ : OneCochain G U) (i j : I) : G.obj (op (U i ⊓ U j)) :=
  γ.ev i j (homOfLE inf_le_left) (homOfLE inf_le_right)

/-- Over a poset, a 1-cochain is determined by its values on binary infima. -/
lemma ev_eq_evInf (γ : OneCochain G U) (i j : I) {T : P} (a : T ⟶ U i) (b : T ⟶ U j) :
    γ.ev i j a b = G.map (homOfLE (le_inf a.le b.le)).op (γ.evInf i j) := by
  have h := γ.ev_precomp i j (homOfLE (le_inf a.le b.le))
    (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)) (homOfLE (inf_le_right : U i ⊓ U j ≤ U j))
  rw [Subsingleton.elim (homOfLE (le_inf a.le b.le) ≫ homOfLE inf_le_left) a,
    Subsingleton.elim (homOfLE (le_inf a.le b.le) ≫ homOfLE inf_le_right) b] at h
  exact h.symm

/-- Restriction commutes with evaluation at binary infima. -/
lemma res_evInf {V : I → P} (γ : OneCochain G U) (f : ∀ i, V i ⟶ U i) (i j : I) :
    (γ.res f).evInf i j
      = G.map (homOfLE (inf_le_inf (f i).le (f j).le)).op (γ.evInf i j) :=
  γ.ev_eq_evInf i j (homOfLE inf_le_left ≫ f i) (homOfLE inf_le_right ≫ f j)

end OneCochain

namespace OneCocycle

/-- The value of a 1-cocycle on the binary infimum `U i ⊓ U j`. -/
abbrev evInf (γ : OneCocycle G U) (i j : I) : G.obj (op (U i ⊓ U j)) :=
  γ.toOneCochain.evInf i j

/-- Restriction commutes with evaluation at binary infima. -/
lemma res_evInf {V : I → P} (γ : OneCocycle G U) (f : ∀ i, V i ⟶ U i) (i j : I) :
    (γ.res f).evInf i j
      = G.map (homOfLE (inf_le_inf (f i).le (f j).le)).op (γ.evInf i j) :=
  γ.toOneCochain.res_evInf f i j

/-- The classical cocycle condition for the pair values of a 1-cocycle: on the triple
infimum, `g i j * g j k = g i k`. -/
lemma evInf_trans (γ : OneCocycle G U) (i j k : I) :
    G.map (homOfLE (inf_le_left : U i ⊓ U j ⊓ U k ≤ U i ⊓ U j)).op (γ.evInf i j) *
        G.map (homOfLE (inf_le_inf_right _ inf_le_right : U i ⊓ U j ⊓ U k ≤ U j ⊓ U k)).op
          (γ.evInf j k) =
      G.map (homOfLE (inf_le_inf_right _ inf_le_left : U i ⊓ U j ⊓ U k ≤ U i ⊓ U k)).op
        (γ.evInf i k) := by
  have h := γ.ev_trans i j k (T := U i ⊓ U j ⊓ U k)
    (homOfLE (inf_le_left.trans inf_le_left)) (homOfLE (inf_le_left.trans inf_le_right))
    (homOfLE inf_le_right)
  simp only [γ.toOneCochain.ev_eq_evInf] at h
  exact h

/-- Build a 1-cocycle over a poset with binary infima from classical pair data: values
`g i j` on the binary infima satisfying the cocycle condition on triple infima. -/
def ofPairs (g : ∀ i j, G.obj (op (U i ⊓ U j)))
    (hg : ∀ i j k,
      G.map (homOfLE (inf_le_left : U i ⊓ U j ⊓ U k ≤ U i ⊓ U j)).op (g i j) *
          G.map (homOfLE (inf_le_inf_right _ inf_le_right : U i ⊓ U j ⊓ U k ≤ U j ⊓ U k)).op
            (g j k) =
        G.map (homOfLE (inf_le_inf_right _ inf_le_left : U i ⊓ U j ⊓ U k ≤ U i ⊓ U k)).op
          (g i k)) :
    OneCocycle G U where
  ev i j _ a b := G.map (homOfLE (le_inf a.le b.le)).op (g i j)
  ev_precomp i j T T' φ a b := map_map G φ.le (le_inf a.le b.le) (g i j)
  ev_trans i j k T a b c := by
    rw [← map_map G (le_inf (le_inf a.le b.le) c.le) inf_le_left (g i j),
      ← map_map G (le_inf (le_inf a.le b.le) c.le) (inf_le_inf_right _ inf_le_right) (g j k),
      ← map_map G (le_inf (le_inf a.le b.le) c.le) (inf_le_inf_right _ inf_le_left) (g i k),
      ← map_mul, hg i j k]

@[simp]
lemma ofPairs_ev (g : ∀ i j, G.obj (op (U i ⊓ U j))) (hg) (i j : I) {T : P}
    (a : T ⟶ U i) (b : T ⟶ U j) :
    (ofPairs g hg).ev i j a b = G.map (homOfLE (le_inf a.le b.le)).op (g i j) :=
  rfl

@[simp]
lemma ofPairs_evInf (g : ∀ i j, G.obj (op (U i ⊓ U j))) (hg) (i j : I) :
    (ofPairs g hg).evInf i j = g i j := by
  change G.map (homOfLE (le_inf (homOfLE inf_le_left).le (homOfLE inf_le_right).le)).op (g i j)
      = g i j
  have h : homOfLE (le_inf (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).le
      (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).le) = 𝟙 (U i ⊓ U j) :=
    Subsingleton.elim _ _
  rw [h, op_id, G.map_id]
  rfl

/-- Round trip: rebuilding a 1-cocycle from its pair values gives it back. -/
lemma evInf_ofPairs (γ : OneCocycle G U) :
    ofPairs (fun i j ↦ γ.evInf i j) (fun i j k ↦ γ.evInf_trans i j k) = γ := by
  ext1
  ext i j T a b
  exact (γ.toOneCochain.ev_eq_evInf i j a b).symm

/-- The coboundary relation in classical pair form: two 1-cocycles over a poset with
binary infima are cohomologous iff there are sections `α i` on the `U i` conjugating the
pair values into each other. -/
lemma isCohomologous_iff_evInf (γ₁ γ₂ : OneCocycle G U) :
    γ₁.IsCohomologous γ₂ ↔ ∃ α : ZeroCochain G U, ∀ i j,
      G.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (α i) * γ₁.evInf i j =
        γ₂.evInf i j * G.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (α j) := by
  constructor
  · rintro ⟨α, hα⟩
    exact ⟨α, fun i j ↦ hα i j (homOfLE inf_le_left) (homOfLE inf_le_right)⟩
  · rintro ⟨α, hα⟩
    refine ⟨α, fun i j T a b ↦ ?_⟩
    have h' := congrArg (G.map (homOfLE (le_inf a.le b.le : T ≤ U i ⊓ U j)).op ·) (hα i j)
    simp only [map_mul, map_map] at h'
    rw [γ₁.toOneCochain.ev_eq_evInf i j a b, γ₂.toOneCochain.ev_eq_evInf i j a b]
    exact h'

end OneCocycle

/-- If the members of the family are mutually comparable (e.g. the family is constant,
as for a cover of a one-point space), then `H1` is trivial: every 1-cocycle is a
coboundary via `α i := γ.evInf`-type data at a base index. -/
theorem H1.subsingleton_of_forall_le (G : Pᵒᵖ ⥤ GrpCat.{w}) (U : I → P)
    (h : ∀ i j, U i ≤ U j) : Subsingleton (H1 G U) := by
  have key : ∀ γ : OneCocycle G U, (1 : OneCocycle G U).IsCohomologous γ := by
    intro γ
    cases isEmpty_or_nonempty I with
    | inl hI => exact ⟨1, fun i ↦ isEmptyElim i⟩
    | inr hI =>
      obtain ⟨i₀⟩ := hI
      refine ⟨fun i ↦ γ.ev i i₀ (𝟙 (U i)) (homOfLE (h i i₀)), fun i j T a b ↦ ?_⟩
      dsimp only
      rw [OneCocycle.one_toOneCochain, OneCochain.one_ev, mul_one,
        OneCochain.ev_precomp, OneCochain.ev_precomp, Category.comp_id, Category.comp_id,
        γ.ev_trans i j i₀ a b (b ≫ homOfLE (h j i₀)),
        Subsingleton.elim (a ≫ homOfLE (h i i₀)) (b ≫ homOfLE (h j i₀))]
  refine ⟨fun x y ↦ ?_⟩
  induction x using Quot.ind with
  | _ γ =>
    induction y using Quot.ind with
    | _ δ =>
      exact Quot.sound ((OneCocycle.equivalence_isCohomologous G U).trans
        ((OneCocycle.equivalence_isCohomologous G U).symm (key γ)) (key δ))

end Poset

/-! ## Commutative values: the group structure on cocycles and `H1` -/

section Comm

variable {G : Cᵒᵖ ⥤ CommGrpCat.{w}} {U V : I → C}

private lemma val_mul_comm {X : Cᵒᵖ}
    (x y : ((G ⋙ forget₂ CommGrpCat GrpCat).obj X)) : x * y = y * x := by
  letI : CommGroup ((G ⋙ forget₂ CommGrpCat GrpCat).obj X) := (G.obj X).str
  exact mul_comm x y

private lemma val_mul_mul_mul_comm {X : Cᵒᵖ}
    (a b c d : ((G ⋙ forget₂ CommGrpCat GrpCat).obj X)) :
    a * b * (c * d) = a * c * (b * d) := by
  letI : CommGroup ((G ⋙ forget₂ CommGrpCat GrpCat).obj X) := (G.obj X).str
  exact mul_mul_mul_comm a b c d

namespace OneCocycle

/-- The product of two 1-cocycles valued in commutative groups (the cocycle condition
for the product cochain uses commutativity). -/
protected def mul (γ₁ γ₂ : OneCocycle (G ⋙ forget₂ CommGrpCat GrpCat) U) :
    OneCocycle (G ⋙ forget₂ CommGrpCat GrpCat) U where
  toOneCochain := γ₁.toOneCochain * γ₂.toOneCochain
  ev_trans i j k T a b c := by
    simp only [OneCochain.mul_ev]
    rw [val_mul_mul_mul_comm, γ₁.ev_trans i j k a b c, γ₂.ev_trans i j k a b c]

/-- The inverse of a 1-cocycle valued in commutative groups. -/
protected def inv (γ : OneCocycle (G ⋙ forget₂ CommGrpCat GrpCat) U) :
    OneCocycle (G ⋙ forget₂ CommGrpCat GrpCat) U where
  toOneCochain := γ.toOneCochain⁻¹
  ev_trans i j k T a b c := by
    simp only [OneCochain.inv_ev]
    rw [← mul_inv_rev, val_mul_comm, γ.ev_trans i j k a b c]

instance : CommGroup (OneCocycle (G ⋙ forget₂ CommGrpCat GrpCat) U) where
  mul := OneCocycle.mul
  one := 1
  inv := OneCocycle.inv
  mul_assoc a b c := toOneCochain_injective (mul_assoc _ _ _)
  one_mul a := toOneCochain_injective (one_mul _)
  mul_one a := toOneCochain_injective (mul_one _)
  inv_mul_cancel a := toOneCochain_injective (inv_mul_cancel _)
  mul_comm a b := toOneCochain_injective (by ext i j T x y; exact val_mul_comm _ _)

@[simp]
lemma mul_toOneCochain (γ₁ γ₂ : OneCocycle (G ⋙ forget₂ CommGrpCat GrpCat) U) :
    (γ₁ * γ₂).toOneCochain = γ₁.toOneCochain * γ₂.toOneCochain :=
  rfl

@[simp]
lemma inv_toOneCochain (γ : OneCocycle (G ⋙ forget₂ CommGrpCat GrpCat) U) :
    (γ⁻¹).toOneCochain = γ.toOneCochain⁻¹ :=
  rfl

@[simp]
lemma mul_res (γ₁ γ₂ : OneCocycle (G ⋙ forget₂ CommGrpCat GrpCat) U)
    (f : ∀ i, V i ⟶ U i) : (γ₁ * γ₂).res f = γ₁.res f * γ₂.res f :=
  rfl

@[simp]
lemma inv_res (γ : OneCocycle (G ⋙ forget₂ CommGrpCat GrpCat) U)
    (f : ∀ i, V i ⟶ U i) : (γ⁻¹).res f = (γ.res f)⁻¹ :=
  rfl

end OneCocycle

lemma OneCohomologyRelation.mul
    {γ₁ γ₂ δ₁ δ₂ : OneCochain (G ⋙ forget₂ CommGrpCat GrpCat) U}
    {α β : ZeroCochain (G ⋙ forget₂ CommGrpCat GrpCat) U}
    (h : OneCohomologyRelation γ₁ γ₂ α) (h' : OneCohomologyRelation δ₁ δ₂ β) :
    OneCohomologyRelation (γ₁ * δ₁) (γ₂ * δ₂) (α * β) := by
  intro i j T a b
  simp only [OneCochain.mul_ev, Cochain₀.mul_apply, map_mul]
  rw [val_mul_mul_mul_comm _ _ (γ₁.ev i j a b), h i j a b, h' i j a b,
    val_mul_mul_mul_comm (γ₂.ev i j a b)]

lemma OneCohomologyRelation.inv {γ₁ γ₂ : OneCochain (G ⋙ forget₂ CommGrpCat GrpCat) U}
    {α : ZeroCochain (G ⋙ forget₂ CommGrpCat GrpCat) U}
    (h : OneCohomologyRelation γ₁ γ₂ α) :
    OneCohomologyRelation γ₁⁻¹ γ₂⁻¹ α⁻¹ := by
  intro i j T a b
  simp only [OneCochain.inv_ev, Cochain₀.inv_apply, map_inv]
  rw [← mul_inv_rev, ← mul_inv_rev,
    val_mul_comm (γ₁.ev i j a b) ((G ⋙ forget₂ CommGrpCat GrpCat).map a.op (α i)),
    h i j a b,
    val_mul_comm (γ₂.ev i j a b) ((G ⋙ forget₂ CommGrpCat GrpCat).map b.op (α j))]

namespace OneCocycle

lemma IsCohomologous.mul {γ₁ γ₂ δ₁ δ₂ : OneCocycle (G ⋙ forget₂ CommGrpCat GrpCat) U}
    (h : γ₁.IsCohomologous γ₂) (h' : δ₁.IsCohomologous δ₂) :
    (γ₁ * δ₁).IsCohomologous (γ₂ * δ₂) := by
  obtain ⟨α, hα⟩ := h
  obtain ⟨β, hβ⟩ := h'
  exact ⟨α * β, hα.mul hβ⟩

lemma IsCohomologous.inv {γ₁ γ₂ : OneCocycle (G ⋙ forget₂ CommGrpCat GrpCat) U}
    (h : γ₁.IsCohomologous γ₂) : (γ₁⁻¹).IsCohomologous (γ₂⁻¹) := by
  obtain ⟨α, hα⟩ := h
  exact ⟨α⁻¹, hα.inv⟩

protected lemma isCohomologous_refl (γ : OneCocycle (G ⋙ forget₂ CommGrpCat GrpCat) U) :
    γ.IsCohomologous γ :=
  (equivalence_isCohomologous _ _).refl γ

end OneCocycle

instance : CommGroup (H1 (G ⋙ forget₂ CommGrpCat GrpCat) U) where
  mul := Quot.map₂ (· * ·) (fun γ _ _ h ↦ γ.isCohomologous_refl.mul h)
    (fun _ _ δ h ↦ h.mul δ.isCohomologous_refl)
  one := 1
  inv := Quot.map (·⁻¹) (fun _ _ h ↦ h.inv)
  mul_assoc a b c := by
    obtain ⟨γ₁⟩ := a; obtain ⟨γ₂⟩ := b; obtain ⟨γ₃⟩ := c
    exact congrArg (Quot.mk _) (mul_assoc γ₁ γ₂ γ₃)
  one_mul a := by
    obtain ⟨γ⟩ := a
    exact congrArg (Quot.mk _) (one_mul γ)
  mul_one a := by
    obtain ⟨γ⟩ := a
    exact congrArg (Quot.mk _) (mul_one γ)
  inv_mul_cancel a := by
    obtain ⟨γ⟩ := a
    exact congrArg (Quot.mk _) (inv_mul_cancel γ)
  mul_comm a b := by
    obtain ⟨γ₁⟩ := a; obtain ⟨γ₂⟩ := b
    exact congrArg (Quot.mk _) (mul_comm γ₁ γ₂)

namespace OneCocycle

@[simp]
lemma class_one : (1 : OneCocycle (G ⋙ forget₂ CommGrpCat GrpCat) U).class = 1 :=
  rfl

@[simp]
lemma class_mul (γ₁ γ₂ : OneCocycle (G ⋙ forget₂ CommGrpCat GrpCat) U) :
    (γ₁ * γ₂).class = γ₁.class * γ₂.class :=
  rfl

@[simp]
lemma class_inv (γ : OneCocycle (G ⋙ forget₂ CommGrpCat GrpCat) U) :
    (γ⁻¹).class = γ.class⁻¹ :=
  rfl

end OneCocycle

/-- Restriction of `H1` classes along an indexwise refinement, as a group homomorphism
(for presheaves of commutative groups). -/
def H1.resHom (f : ∀ i, V i ⟶ U i) :
    H1 (G ⋙ forget₂ CommGrpCat GrpCat) U →* H1 (G ⋙ forget₂ CommGrpCat GrpCat) V where
  toFun := H1.res f
  map_one' := rfl
  map_mul' x y := by
    obtain ⟨γ₁⟩ := x; obtain ⟨γ₂⟩ := y
    exact congrArg (Quot.mk _) (γ₁.mul_res γ₂ f)

@[simp]
lemma H1.resHom_apply (f : ∀ i, V i ⟶ U i) (x : H1 (G ⋙ forget₂ CommGrpCat GrpCat) U) :
    H1.resHom f x = H1.res f x :=
  rfl

end Comm

end CategoryTheory.PresheafOfGroups
