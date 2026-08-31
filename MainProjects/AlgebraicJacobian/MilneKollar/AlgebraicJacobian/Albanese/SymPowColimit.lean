/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Albanese.SymPowInterface

/-!
# The symmetric power is a colimit of the permutation action

`Albanese/SymPowInterface.lean` names the universal property of `Sym^n C` as data
(`SymPowData`) and proves Milne's Albanese argument over it. It also records the honest
limitation: the *bare* structure is trivially inhabited (`symPowDataTrivial`, take
`proj := 𝟙`), so what the downstream theorems quantify over is the **pair**
`(D, hproj)` with `hproj : ∀ σ, permAut C σ ≫ D.proj = D.proj`, and that pair had only
one witness — `n = 1`.

This file removes that limitation by identifying what the pair *is*.

## The identification

Let `permDiagram C n : SingleObj (Equiv.Perm (Fin n)) ⥤ K` be the one-object diagram of
the `S_n`-action on `C^n` by `permAut`. Then:

* `symPowOfColimit` — a colimit of `permDiagram C n` **is** a `SymPowData C n`, and
* `symPowOfColimit_proj_perm` — its projection is symmetric **for free**: the symmetry
  hypothesis is literally `colimit.w`, the cocone condition;
* `SymPowData.isColimit` — conversely, any pair `(D, hproj)` *is* a colimit of the same
  diagram.

So the pair the Albanese theorems consume is not merely *implied by* a quotient — it is
**equivalent** to a colimit of the permutation action. That is the categorical content of
Milne III.3 Proposition 3.1 separated from its affine-and-glue implementation.

## Why this is a reduction and not a restatement

Three things change, and each is checked below rather than asserted.

1. **The trivial witness is refuted, in the tree.** `permAut_swap_ne_id` exhibits a
   concrete `K` (`Type`), a concrete object (`Bool`) and `n = 2` at which
   `permAut ≠ 𝟙`; hence `symPowDataTrivial` genuinely fails `hproj` there
   (`symPowDataTrivial_not_proj_perm`). The `SymPowInterface` header asserted this;
   nothing had checked it.
2. **The pair is inhabited at every `n`, not just `n = 1`**, in any cartesian monoidal
   category with the relevant colimit — `symPowData_of_hasColimit`. The interface's
   `n = 1`-only caveat was a statement about `K`, not about `n`.
3. **The obligation becomes a mathlib-shaped one.** "Construct `Sym^n C`" is replaced by
   `HasColimit (permDiagram C n)`. For the two categories checked here — `Type u` and
   affine `k`-schemes `(Under k)ᵒᵖ` — mathlib *already* discharges it, so the pair is
   inhabited there at every `n` with no new geometry (`symPowDataType`,
   `symPowDataAffine`).

## What is still open, stated precisely

`Sym^n C` for `C` a **proper** curve in `Over (Spec k̄)`. `Over (Spec k̄)` is not known to
have these colimits: the affine construction glues, and gluing is exactly the part of
Milne III.3.1 that this file does not do. The gain is not that the curve case is done —
it is that the remaining obligation is now one named instance about one named diagram,
the symmetry half is discharged permanently, and the affine case is *proved* rather than
scoped at hundreds of lines.

Note also the direction of the equivalence: because `SymPowData.isColimit` shows the pair
*is* a colimit, no future construction can supply the pair without supplying that colimit.
The reduction is therefore lossless — it cannot have replaced the problem with a
strictly harder one.

## References

Milne, *Abelian Varieties*, §III.3 Proposition 3.1 (the symmetric power), p. 94; §III.6
Proposition 6.1, p. 104. Blueprint `def:symmetric_power_curve`. The consumer is
`Albanese/AlbaneseFromData.lean`.
-/

set_option autoImplicit false

universe v u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace CategoryTheory

variable {K : Type u} [Category.{v} K] [CartesianMonoidalCategory K] [HasFiniteProducts K]

/-! ## §1. The permutation action as a diagram

`MonObj.permAut` (`Albanese/GrpObjFoldSum.lean`) gives the factor-permuting endomorphism
of `C^n`. Bundling it as a monoid homomorphism into `End (C^n)` turns the `S_n`-action
into a functor out of `SingleObj (Equiv.Perm (Fin n))`, which is the shape mathlib's
colimit API consumes.

One convention point worth stating, since it is the only place a sign can go wrong:
composition in `End X` is `f * g = g ≫ f`, so a *homomorphism* out of `Equiv.Perm (Fin n)`
must use `σ ↦ permAut C σ⁻¹`. With that inverse the multiplicativity is `rfl` after
projecting; without it one gets an anti-homomorphism. -/

/-- **The `S_n`-action on `C^n`, as a monoid homomorphism into `End (C^n)`.**

Sends `σ` to `permAut C σ⁻¹`. The inverse is forced by mathlib's `End` convention
(`f * g = g ≫ f`); see the section note. -/
noncomputable def permEnd (C : K) (n : ℕ) :
    Equiv.Perm (Fin n) →* End (∏ᶜ (fun _ : Fin n => C)) where
  toFun σ := MonObj.permAut C σ⁻¹
  map_one' := by
    apply Pi.hom_ext; intro i
    rw [MonObj.permAut_π]; simp
  map_mul' σ τ := by
    apply Pi.hom_ext; intro i
    change MonObj.permAut C (σ * τ)⁻¹ ≫ _ = (MonObj.permAut C τ⁻¹ ≫ MonObj.permAut C σ⁻¹) ≫ _
    rw [MonObj.permAut_π, Category.assoc, MonObj.permAut_π, MonObj.permAut_π]
    rfl

/-- **The permutation-action diagram.** The one-object diagram in `K` whose single value
is `C^n` and whose endomorphisms are the factor permutations. A colimit of it is the
quotient `C^n / S_n`. -/
noncomputable def permDiagram (C : K) (n : ℕ) : SingleObj (Equiv.Perm (Fin n)) ⥤ K :=
  SingleObj.functor (permEnd C n)

variable (C : K) (n : ℕ)

omit [CartesianMonoidalCategory K] in
/-- The diagram's value at the unique object is `C^n`. -/
theorem permDiagram_obj (j : SingleObj (Equiv.Perm (Fin n))) :
    (permDiagram C n).obj j = ∏ᶜ (fun _ : Fin n => C) := rfl

omit [CartesianMonoidalCategory K] in
/-- **The action, expressed as a diagram map.** `permAut C σ` is the diagram's map at
`σ⁻¹`; the double inverse is the `End`-convention bookkeeping of `permEnd`. This is the
bridge every proof below crosses. -/
theorem permAut_eq_map (σ : Equiv.Perm (Fin n)) :
    MonObj.permAut C σ = (permDiagram C n).map (SingleObj.toEnd (Equiv.Perm (Fin n)) σ⁻¹) := by
  change MonObj.permAut C σ = MonObj.permAut C σ⁻¹⁻¹
  rw [inv_inv]

omit [CartesianMonoidalCategory K] in
/-- **Every cocone leg is symmetric.** This is the cocone condition `Cocone.w` read
through `permAut_eq_map`, and it is the reason the symmetry hypothesis of `SymPowData`
costs nothing on the colimit side. -/
theorem cocone_app_perm (c : Cocone (permDiagram C n)) (σ : Equiv.Perm (Fin n)) :
    MonObj.permAut C σ ≫ c.ι.app (SingleObj.star _) = c.ι.app (SingleObj.star _) := by
  rw [permAut_eq_map C n σ]
  exact c.w (SingleObj.toEnd (Equiv.Perm (Fin n)) σ⁻¹)

/-- **A symmetric morphism out of `C^n` is a cocone.** The converse packaging of
`cocone_app_perm`: `S_n`-invariance of `h` is exactly the cocone condition. -/
noncomputable def symCocone {T : K} (h : (∏ᶜ (fun _ : Fin n => C)) ⟶ T)
    (hsym : ∀ σ : Equiv.Perm (Fin n), MonObj.permAut C σ ≫ h = h) :
    Cocone (permDiagram C n) where
  pt := T
  ι :=
    { app := fun _ => h
      naturality := by
        intro X Y f
        change MonObj.permAut C (f : Equiv.Perm (Fin n))⁻¹ ≫ h = h ≫ 𝟙 T
        rw [Category.comp_id]
        exact hsym _ }

/-! ## §2. A colimit of the action is a `SymPowData`, with symmetry for free

This is the forward half of the identification. Note which part is doing the work: the
universal property of `SymPowData` is `colimit.desc` plus `colimit.hom_ext`, and the
symmetry hypothesis `hproj` — the half that ruled out the trivial witness and had only
an `n = 1` witness before — is `colimit.w`. Nothing is assumed about `n`. -/

section OfColimit

variable [HasColimit (permDiagram C n)]

/-- **The symmetric power from a colimit of the permutation action.**

`carrier := colimit (permDiagram C n)`, `proj := colimit.ι`, and the universal property is
`colimit.desc` — a symmetric `h` is a cocone by `symCocone`, and uniqueness is
`colimit.hom_ext` on the one-object index category. -/
noncomputable def symPowOfColimit : SymPowData C n where
  carrier := colimit (permDiagram C n)
  proj := colimit.ι (permDiagram C n) (SingleObj.star _)
  desc := fun {T} h hsym => by
    have hd : colimit.ι (permDiagram C n) (SingleObj.star _)
        ≫ colimit.desc (permDiagram C n) (symCocone C n h hsym) = h :=
      colimit.ι_desc (symCocone C n h hsym) (SingleObj.star _)
    refine ⟨colimit.desc (permDiagram C n) (symCocone C n h hsym), hd, ?_⟩
    intro u hu
    exact colimit.hom_ext fun j => by
      obtain rfl : j = SingleObj.star _ := Subsingleton.elim _ _
      exact hu.trans hd.symm

omit [CartesianMonoidalCategory K] in
@[simp]
theorem symPowOfColimit_carrier :
    (symPowOfColimit C n).carrier = colimit (permDiagram C n) := rfl

omit [CartesianMonoidalCategory K] in
@[simp]
theorem symPowOfColimit_proj :
    (symPowOfColimit C n).proj = colimit.ι (permDiagram C n) (SingleObj.star _) := rfl

omit [CartesianMonoidalCategory K] in
/-- **The symmetry hypothesis, for free.** The projection of `symPowOfColimit` is
`S_n`-symmetric because that is the cocone condition `colimit.w`.

This is the declaration that changes the interface's status: `SymPowInterface.lean` needs
the *pair* `(D, hproj)`, and here `hproj` comes with the object at no cost and at every
`n`. -/
theorem symPowOfColimit_proj_perm (σ : Equiv.Perm (Fin n)) :
    MonObj.permAut C σ ≫ (symPowOfColimit C n).proj = (symPowOfColimit C n).proj := by
  have h := colimit.w (permDiagram C n) (SingleObj.toEnd (Equiv.Perm (Fin n)) σ⁻¹)
  change MonObj.permAut C σ ≫ colimit.ι (permDiagram C n) (SingleObj.star _) = _
  rw [permAut_eq_map C n σ]
  exact h

omit [CartesianMonoidalCategory K] in
/-- **The pair, packaged.** Existence of the object the Albanese theorems quantify over,
in the form a call site consumes: a `SymPowData` *together with* its symmetry. -/
theorem symPowData_of_hasColimit :
    ∃ D : SymPowData C n, ∀ σ : Equiv.Perm (Fin n),
      MonObj.permAut C σ ≫ D.proj = D.proj :=
  ⟨symPowOfColimit C n, symPowOfColimit_proj_perm C n⟩

end OfColimit

/-! ## §3. Conversely: the pair *is* a colimit

The other half of the identification, and the one that makes the reduction lossless. Any
`SymPowData` whose projection is symmetric exhibits its carrier as a colimit of
`permDiagram C n`.

Consequence worth stating explicitly, because it is what rules out having traded the
problem for a harder one: nobody can supply the pair `(D, hproj)` *without* supplying this
colimit. So `HasColimit (permDiagram C n)` is not a sufficient condition that might be
stronger than needed — it is equivalent to the thing the Albanese argument consumes. -/

section ToColimit

/-- The cocone attached to a `SymPowData` with symmetric projection. -/
noncomputable def SymPowData.cocone (D : SymPowData C n)
    (hproj : ∀ σ : Equiv.Perm (Fin n), MonObj.permAut C σ ≫ D.proj = D.proj) :
    Cocone (permDiagram C n) where
  pt := D.carrier
  ι :=
    { app := fun _ => D.proj
      naturality := by
        intro X Y f
        change MonObj.permAut C (f : Equiv.Perm (Fin n))⁻¹ ≫ D.proj = D.proj ≫ 𝟙 _
        rw [Category.comp_id]
        exact hproj _ }

/-- **The pair is a colimit.** A `SymPowData` with symmetric projection is precisely a
colimit of the permutation action — its universal property *is* the colimit property,
transported across the fact that a cocone on a one-object diagram is a symmetric
morphism (`cocone_app_perm`). -/
noncomputable def SymPowData.isColimit (D : SymPowData C n)
    (hproj : ∀ σ : Equiv.Perm (Fin n), MonObj.permAut C σ ≫ D.proj = D.proj) :
    IsColimit (D.cocone C n hproj) where
  desc c := (D.desc (c.ι.app (SingleObj.star _)) (cocone_app_perm C n c)).choose
  fac c j := by
    obtain rfl : j = SingleObj.star _ := Subsingleton.elim _ _
    exact (D.desc (c.ι.app (SingleObj.star _)) (cocone_app_perm C n c)).choose_spec.1
  uniq c u hu :=
    (D.desc (c.ι.app (SingleObj.star _)) (cocone_app_perm C n c)).choose_spec.2 u
      (hu (SingleObj.star _))

omit [CartesianMonoidalCategory K] in
/-- **The obligation is exactly a `HasColimit`.** Supplying the pair the Albanese
theorems quantify over is equivalent to the diagram having a colimit — so replacing
"construct `Sym^n C`" by `HasColimit (permDiagram C n)` neither weakens nor strengthens
the problem. -/
theorem hasColimit_permDiagram_iff :
    HasColimit (permDiagram C n) ↔
      ∃ D : SymPowData C n, ∀ σ : Equiv.Perm (Fin n),
        MonObj.permAut C σ ≫ D.proj = D.proj := by
  refine ⟨fun _ => symPowData_of_hasColimit C n, fun ⟨D, hproj⟩ => ?_⟩
  exact ⟨⟨⟨D.cocone C n hproj, D.isColimit C n hproj⟩⟩⟩

end ToColimit

end CategoryTheory

/-! ## §4. The trivial witness is genuinely refuted at `n = 2`

`SymPowInterface.lean` keeps `symPowDataTrivial` (`proj := 𝟙`) as its acceptance test and
states that it fails the symmetry hypothesis for `n ≥ 2` "since it would force
`permAut C σ = 𝟙`". That was an *assertion*: nothing in the tree had exhibited a category
and an object where `permAut` at a transposition really differs from the identity, so the
argument for why the interface is not vacuous rested on an unchecked step.

It is checked here, concretely: `K = Type`, `C = Bool`, `n = 2`, `σ = swap 0 1`. Evaluating
both projections at the tuple `(true, false)` separates them. -/

namespace CategoryTheory

open Limits

/-- The tuple `(true, false)` in `Bool²`, as a `Type`-morphism out of `Bool`. Used only to
separate the two projections. -/
noncomputable def boolPairTuple : (Bool : Type) ⟶ (∏ᶜ fun _ : Fin 2 => (Bool : Type)) :=
  Pi.lift (P := (Bool : Type))
    (fun i : Fin 2 => TypeCat.ofHom (fun _ : Bool => decide (i = 0)))

/-- **`permAut` at a transposition is not the identity.** Witnessed in `Type` at `Bool`
and `n = 2`: composing with the `0`-th projection turns `permAut (swap 0 1) = 𝟙` into
`π₁ = π₀`, which the tuple `(true, false)` refutes.

This is the fact that makes `SymPowData`'s symmetry hypothesis non-vacuous for `n ≥ 2`. -/
theorem permAut_swap_ne_id :
    MonObj.permAut (Bool : Type) (Equiv.swap (0 : Fin 2) 1) ≠ 𝟙 _ := by
  intro hc
  have h0 := congrArg (fun f => f ≫ Pi.π (fun _ : Fin 2 => (Bool : Type)) 0) hc
  simp only [MonObj.permAut_π, Category.id_comp] at h0
  rw [Equiv.swap_apply_left] at h0
  have h1 := congrArg (fun f => boolPairTuple ≫ f) h0
  simp only [boolPairTuple, Pi.lift_π] at h1
  have h2 := congrArg
    (fun (f : (Bool : Type) ⟶ (Bool : Type)) => ConcreteCategory.hom f true) h1
  simp at h2

/-- **The general criterion: two distinct global points defeat the trivial datum.**

If `C` has two distinct global points `p ≠ q : 𝟙_ K ⟶ C`, then `permAut C` at a
transposition is not the identity — evaluate the two projections at the pair `(p, q)`.

This is stated in an arbitrary cartesian monoidal `K`, so unlike `permAut_swap_ne_id`
(which lives in `Type`) it applies **in `Over (Spec k̄)` at the actual curve**: a smooth
proper geometrically irreducible curve over an algebraically closed field has more than one
`k̄`-point, so the pair `(D, hproj)` is a non-trivial demand *where the Albanese theorems are
instantiated*, not merely in a toy category.

That distinction is the point of having this lemma as well as the `Type` witness: a
non-vacuity argument has to be run in the category the application uses. -/
theorem permAut_swap_ne_id_of_points {K : Type u} [Category.{v} K]
    [CartesianMonoidalCategory K] [HasFiniteProducts K]
    {C : K} (p q : 𝟙_ K ⟶ C) (hpq : p ≠ q) :
    MonObj.permAut C (Equiv.swap (0 : Fin 2) 1) ≠ 𝟙 _ := by
  intro hc
  set t : 𝟙_ K ⟶ (∏ᶜ fun _ : Fin 2 => C) :=
    Pi.lift (fun i : Fin 2 => if i = 0 then p else q) with ht
  have h0 := congrArg (fun f => f ≫ Pi.π (fun _ : Fin 2 => C) 0) hc
  simp only [MonObj.permAut_π, Category.id_comp] at h0
  rw [Equiv.swap_apply_left] at h0
  have h1 : t ≫ Pi.π (fun _ : Fin 2 => C) 1 = t ≫ Pi.π (fun _ : Fin 2 => C) 0 := by rw [h0]
  rw [ht, Pi.lift_π, Pi.lift_π] at h1
  simp at h1
  exact hpq h1.symm

/-- **And the converse boundary: at a terminal object the trivial datum *does* satisfy
`hproj`.** `permAut C σ = 𝟙` whenever `C` is terminal, since any two morphisms into a
terminal object agree.

So the claim "the trivial datum fails `hproj` for `n ≥ 2`" is **false as a general
statement about every `C`** — it is true exactly at objects with enough points to separate
the projections (`permAut_swap_ne_id_of_points`). `SymPowInterface.lean`'s docstring
originally made the unqualified claim; this pair of lemmas is the correction, and the
qualification matters because a class satisfied by a trivial witness demands nothing. -/
theorem permAut_eq_id_of_isTerminal {K : Type u} [Category.{v} K]
    [CartesianMonoidalCategory K] [HasFiniteProducts K]
    {C : K} (hC : IsTerminal C) {n : ℕ}
    (σ : Equiv.Perm (Fin n)) : MonObj.permAut C σ = 𝟙 _ := by
  refine Pi.hom_ext _ _ fun i => ?_
  rw [MonObj.permAut_π, Category.id_comp]
  exact hC.hom_ext _ _

/-- **The trivial datum fails the symmetry hypothesis.** So `symPowDataTrivial` is not a
witness for the pair `(D, hproj)` at `n = 2`, and the `SymPowInterface` header's
contrastive claim is now a checked fact rather than a remark. -/
theorem symPowDataTrivial_not_proj_perm :
    ¬ (∀ σ : Equiv.Perm (Fin 2),
        MonObj.permAut (Bool : Type) σ ≫ (symPowDataTrivial (Bool : Type) 2).proj
          = (symPowDataTrivial (Bool : Type) 2).proj) := by
  intro h
  refine permAut_swap_ne_id ?_
  have h2 := h (Equiv.swap 0 1)
  change MonObj.permAut (Bool : Type) (Equiv.swap 0 1) ≫ 𝟙 _ = 𝟙 _ at h2
  rwa [Category.comp_id] at h2

end CategoryTheory

/-! ## §5. Where mathlib already discharges the obligation

Two categories where `HasColimit (permDiagram C n)` is available with no new geometry, so
the pair `(D, hproj)` is inhabited **at every `n`**:

* `Type u` — colimits of every shape;
* `(Under k)ᵒᵖ`, the opposite of the category of `k`-algebras. Mathlib supplies its colimits
  as limits in `Under k`, so `symPowData_of_hasColimit` applies at every `n`.

**State this one carefully — an earlier draft of this header did not.** What is *proved* is
that the pair `(D, hproj)` exists in `(Under k)ᵒᵖ` at every `n`. Two further things are
*expected* and are **not** proved here:

* that `(Under k)ᵒᵖ` is the category of affine `k`-schemes. Morally it is, via
  `Over.opEquivOpUnder` and `AffineScheme.equivCommRingCat`, but no declaration below builds
  that bridge;
**The carrier: NOW NAMED, elsewhere (2026-07-29, run 0069 r7).** This bullet used to end with
"**The carrier is not named in Lean**", and it no longer holds. It is *still* true that nothing
in **this file** names it — `symPowData_affineAlgebra` below takes its colimit from
`(Under k)ᵒᵖ`'s cocompleteness, so the object it produces is an anonymous `colimit` and
`mem_sections_singleObj_iff` remains only the *reason to expect* the identification, being a
statement about `SingleObj G ⥤ Type` that mentions neither `CommRingCat` nor `Spec`. What changed
is that the identification is now a theorem:

`PiTensorProduct.colimitPermDiagramIsoFixed` (`Albanese/SymPowAffineQuotient.lean`) proves

`colimit (permDiagram (op (mkUnder k A)) n) ≅ op (fixedUnder k (Perm (Fin n)) (⨂[k] _ : Fin n, A))`

— the colimit of the diagram *this file* takes a colimit of is `Spec_k` of Milne's
`(A^{⊗ n})^{S_n}`. It rests on two comparisons that were landed separately and never composed:
`SymPowAffineCarrier.tensorPowerOpIsoPiObj` (the `n`-fold product in `(Under k)ᵒᵖ` is `op` of the
tensor power, actions matched — and the match carries `e⁻¹`) and
`SymPowInvariantsUnder.fixedCoconeUnderIsColimitOp` (the quotient is `op` of the invariant
subalgebra), glued by a diagram isomorphism plus the `(SingleObj G)ᵒᵖ` index transport.

One thing NOT to read into it: the accompanying `hasColimit_permDiagram_op_mkUnder` is **not** a
new fact — cocompleteness already gives that instance, `infer_instance` discharges it. Only the
*iso* is new, because only a statement mentioning the object can name it.

So read this section as: *the affine algebra case of the interface is inhabited at every
`n`, from mathlib's colimits, with no construction written* — and, since run 0069 r7, *with the
resulting object identified elsewhere* by `colimitPermDiagramIsoFixed`. Still not as: *Milne III.3
Proposition 3.1's affine half is formalised in this file* — the identification is a theorem of
`Albanese/SymPowAffineQuotient.lean`, it holds at the `mkUnder` instantiations rather than the
arbitrary `X` quantified over below, and the second bridge (that `(Under k)ᵒᵖ` **is** affine
`k`-schemes) is still unbuilt, so all of it is `k`-algebra language rather than `Spec`-language.

What is likewise *not* here is the curve case: `Over (Spec k̄)` with `C` proper. The gluing
of the affine quotients — the remaining half of Milne III.3.1 — is what would give that, and
it is the honest boundary. -/

namespace CategoryTheory

open Limits

/-- **A one-object diagram's sections are its invariants.** For a diagram indexed by
`SingleObj G`, lying in the `sections` set is equivalent to being fixed by every `g : G` —
the many-object quantifier collapses because the index category has one object and
`SingleObj.toEnd` is an equivalence onto its endomorphisms.

**What this is for, stated so it does not overclaim.** It is the reason to *expect* that the
affine colimit is `Spec` of the invariant subring of the `n`-fold tensor power — Milne's
`(A^{⊗n})^{S_n}` in III.3 Proposition 3.1 — because limits in `CommRingCat` are computed as
sections (`CommRingCat.limitCone`) and, by this lemma, a one-object diagram's sections are
its fixed points.

It is **not** a proof of that identification: the statement below is about
`SingleObj G ⥤ Type` and mentions neither `CommRingCat` nor `Spec` nor a tensor power. So
the carrier is *not* named in Lean; see the §5 header. An earlier version of this docstring
claimed it was, which is why the caveat is spelled out here rather than only there. -/
theorem mem_sections_singleObj_iff {G : Type u} [Group G] (F : SingleObj G ⥤ Type v)
    (x : (j : SingleObj G) → F.obj j) :
    x ∈ F.sections ↔
      ∀ g : G, F.map (SingleObj.toEnd G g) (x (SingleObj.star G)) = x (SingleObj.star G) := by
  refine ⟨fun hx g => hx (SingleObj.toEnd G g), fun h j j' f => ?_⟩
  obtain rfl : j = SingleObj.star G := Subsingleton.elim _ _
  obtain rfl : j' = SingleObj.star G := Subsingleton.elim _ _
  exact h ((SingleObj.toEnd G).symm f)

/-- **Every `n`, in `Type`.** The symmetric power interface with its symmetry hypothesis,
inhabited at all `n` — `Type` has all colimits.

Contrast with `symPowDataOne`: that was `n = 1` only. Here `n` is arbitrary, so the
statements the Albanese argument quantifies over are non-vacuous in the range where the
group-law step is genuinely exercised. -/
theorem symPowData_type (X : Type u) (n : ℕ) :
    ∃ D : SymPowData X n, ∀ σ : Equiv.Perm (Fin n),
      MonObj.permAut X σ ≫ D.proj = D.proj :=
  symPowData_of_hasColimit X n

/-- **Every `n`, in the opposite of `k`-algebras** — the affine algebra case.

`(Under k)ᵒᵖ` has all colimits (they are limits in `Under k`), so the pair `(D, hproj)` is
inhabited there at every `n`, with no construction written.

**What this is and is not.** It is the inhabitation statement, for an *arbitrary* `X`. It is
*not* a formalisation of Milne III.3 Proposition 3.1's affine half, which also identifies the
object; two bridges are needed for that, and as of 2026-07-29 exactly one of them is built:

* the carrier is `Spec` of the invariant subring of the `n`-fold tensor power — **built**, at
  `X = op (mkUnder k A)`, by `PiTensorProduct.colimitPermDiagramIsoFixed`
  (`Albanese/SymPowAffineQuotient.lean`). So `mem_sections_singleObj_iff` is no longer the only
  reason to expect it. Note the instantiation: this theorem quantifies over every `X : (Under k)ᵒᵖ`
  and the identification is available only at the `mkUnder` ones, which is the affine case Milne
  states it for;
* `(Under k)ᵒᵖ` *is* the category of affine `k`-schemes, via `Over.opEquivOpUnder` and
  `AffineScheme.equivCommRingCat` — **still not built**, so everything above is `k`-algebra
  language rather than `Spec`-language. See the §5 header. -/
theorem symPowData_affineAlgebra (k : CommRingCat.{u}) (X : (Under k)ᵒᵖ) (n : ℕ) :
    letI : CartesianMonoidalCategory (Under k)ᵒᵖ := ofHasFiniteProducts
    ∃ D : SymPowData X n, ∀ σ : Equiv.Perm (Fin n),
      MonObj.permAut X σ ≫ D.proj = D.proj :=
  letI : CartesianMonoidalCategory (Under k)ᵒᵖ := ofHasFiniteProducts
  symPowData_of_hasColimit X n

end CategoryTheory

/-! ## §6. The curve case: the obligation is a statement about `Scheme`, not about
`Over (Spec k̄)`

The Albanese connector lives in `Over (Spec k̄)`, so one might expect the missing
construction to be an over-category one, with structure-map bookkeeping on top of the
quotient. It is not: `Over.forget` **creates** colimits, so a colimit of the permutation
action in `Scheme` gives one in `Over (Spec k̄)` for free.

That removes a whole layer from the remaining work: the leg's single open obligation is
`HasColimit (permDiagram C n)` — one diagram, for the curve at hand — and by
`hasColimit_permDiagram_iff` that is exactly equivalent to the datum the Albanese theorems
consume.

**Do not strengthen it to `HasColimitsOfShape (SingleObj (Equiv.Perm (Fin n))) Scheme`.**
That form is tempting because it reads as "schemes have finite-group quotients", but it is
strictly stronger, it is *not* what the equivalence covers, and by the availability table
below it is believed false at this pin — so a theorem carrying it would be vacuously true
and its obligation undischargeable in principle. The per-diagram binder is satisfiable and
is the honest residue. `symPowData_over_of_scheme_colimits` below is stated with the
quantified form deliberately, as a *sufficient* condition and nothing more.

**What is and is not available for it, measured at this pin** (so the next session does not
re-derive the search):

* `HasCoproducts Scheme` — **available**. So the disjoint-union half of any glueing is free.
* `HasCoequalizers Scheme`, `HasPushouts Scheme` — **not available**, neither synthesizes.
  This is the actual obstruction: a colimit over `SingleObj G` is a coequalizer-type colimit,
  and schemes do not admit them in general (the quotient of a scheme by an equivalence
  relation need not be a scheme — cf. the standing caveat in inbox `I-0074` about
  algebraic spaces).
* `AlgebraicGeometry.Scheme.GlueData` — **available**, with `GlueData.openCover`. This is the
  tool Milne's affine-and-glue route would use: build the affine quotients (done here, at
  every `n`) and glue them along the standard open cover.

So the honest shape of the remaining work is *not* "wait for mathlib to add scheme
quotients". It is: assemble a `Scheme.GlueData` from the affine quotients of
`symPowData_affineAlgebra`, which is the second half of Milne III.3 Proposition 3.1 and needs the
compatibility of those quotients on overlaps. That is real work, but it is bounded and its
inputs now exist.

**One sharpening, because it is exactly where the affine result stops.** `Scheme.Spec` is
fully faithful and preserves limits, so the affine quotient's universal property transfers
into `Scheme` *against affine test objects*. It does **not** transfer against an arbitrary
scheme target: a morphism out of the quotient into a non-affine `T` is not detected by the
affine story, and that is precisely the gap gluing closes. So "the affine case is proved"
should be read as *the affine quotient exists and is `Spec` of the invariants*, not as *the
symmetric power of an affine curve chart already satisfies the universal property Milne
needs*. The second reading would be the over-claim, and it is the one to avoid. -/

namespace AlgebraicGeometry

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

/-- **The curve case reduces to `Scheme`.** If `Scheme` has colimits of the
`S_n`-action shape, then the pair the Albanese theorems quantify over exists for any
`k̄`-scheme `C` — in particular for a proper curve.

The transfer is free: `Over.forget` creates colimits, so no compatibility with the
structure morphism has to be checked. Compare `Albanese/AlbaneseFromData.lean`'s
`comp_hom_of_descent_eq`, where the analogous crossing for the *descent* datum also turned
out to be automatic.

**This hypothesis is SUFFICIENT, not the leg's residue.** It is the shape-quantified form,
strictly stronger than `HasColimit (permDiagram C n)` and believed false at this pin (§6),
so this theorem is probably vacuous as stated. It is kept because the *implication* is the
content — it is what shows the over-category layer costs nothing — and it is stated in the
strong form because that is the form in which "schemes have finite-group quotients" would
arrive. The obligation to discharge is the per-diagram one. -/
theorem symPowData_over_of_scheme_colimits {kbar : Type u} [Field kbar]
    (C : Over (Spec (.of kbar))) (n : ℕ)
    [HasColimitsOfShape (SingleObj (Equiv.Perm (Fin n))) Scheme.{u}] :
    ∃ D : SymPowData C n, ∀ σ : Equiv.Perm (Fin n),
      MonObj.permAut C σ ≫ D.proj = D.proj :=
  symPowData_of_hasColimit C n

end AlgebraicGeometry
