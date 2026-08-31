/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.JacobianDataAbel

/-!
# The genus-zero Jacobian is the terminal object, and its universal property is free

S11 of the Wave-6 plan: Milne assumes `0 < g` throughout III §§5-6, but the frozen
challenge target `exists_unique_ofCurve_comp` carries **no genus hypothesis**, so the
`g = 0` case has to be discharged separately.  The recon
(`informal/w6-albanese-port-recon.md` §3, row S11) sized it as `Jacobian C ≅ 𝟙_` plus
Milne I 3.9 (every rational map `ℙ¹ ⇢ A` to an abelian variety is constant), with "zero
portable or landed support".

**Milne I 3.9 is needed only for existence.**  The `∃!` splits, and the two clauses have
very different prices:

* *uniqueness* of the factorisation `f = ofCurve P ≫ g` is `cancel_epi`, needing only
  that `d.ofCurve P` is an epimorphism.  In the degenerate case that is nearly free:
  `d.J` is the base, so `d.ofCurve P` is the structure morphism of a nonempty
  `k`-scheme, every morphism to `Spec` of a field is flat, and flat + surjective is epi;
* *existence* of some `g` is where the geometry lives — it is exactly the constancy of
  `f`, i.e. Milne I 3.9.  This file does not prove it and does not pretend to; it is an
  explicit hypothesis of `existsUnique_ofCurve_comp_of_epi`.

So the file's contribution is the reduction, plus a precise account of what is left.

## The reduction (this file's actual theorem)

`isTerminal_of_pic0Subgroup_eq_bot`: **if `Pic⁰_{C/k}(T)` is the trivial subgroup for
every test `T`, the representing object `d.J` is a terminal object of
`Over (Spec k)`.**  This is pure transport of the universal property
`homEquiv : (T ⟶ d.J) ≃ pic0Subgroup C T` across `Subsingleton`/`Nonempty`, and it is
free: no genus, no `ℙ¹`, no rational maps, no Milne I 3.9.

Note carefully what the hypothesis is.  It is *not* `genus C = 0`.  Deducing
`pic0Subgroup C T = ⊥` from `genus C = 0` is a genuine piece of curve theory — for
`T = Spec k` it is the classical "a genus-0 curve with a rational point is `ℙ¹`, whose
degree-0 classes are trivial", and for general `T` it is the relative statement.  That
implication is **not** proved here and is not claimed; it is isolated as the single
mathematical debt of S11, and it is where all the cost of the leaf actually sits.  What
this file buys is that the debt is *one implication about Picard groups* rather than the
Milne I 3.9 geometry the recon budgeted for.

## Main declarations

* `AlgebraicGeometry.JacobianData.subsingleton_hom_of_pic0Subgroup_eq_bot` — the
  `Hom`-set into `d.J` is a subsingleton when the degree-zero group vanishes.
* `AlgebraicGeometry.JacobianData.isTerminal_of_pic0Subgroup_eq_bot` — **the
  reduction**: vanishing `Pic⁰` on all tests makes `d.J` terminal.
* `AlgebraicGeometry.JacobianData.epi_of_epi_left` / `isIso_hom_of_isTerminal` /
  `epi_of_isTerminal_of_surjective` — the `Epi (d.ofCurve P)` input, **discharged** from
  terminality plus nonemptiness of the curve rather than assumed.
* `AlgebraicGeometry.JacobianData.existsUnique_ofCurve_comp_of_epi` — the Albanese `∃!`
  from `Epi (d.ofCurve P)` plus bare existence.  The existence hypothesis is stated
  explicitly rather than hidden.
* `AlgebraicGeometry.JacobianData.existsUnique_ofCurve_comp_of_pic0Subgroup_eq_bot` —
  **S11 assembled**: vanishing `Pic⁰` plus a nonempty curve give the uniqueness clause
  outright, leaving only existence.
* `AlgebraicGeometry.JacobianData.ofCurve_eq_of_isTerminal` — in the terminal case the
  Abel–Jacobi map is the unique morphism `C ⟶ d.J`, so it carries no information; this
  is the precise sense in which the genus-0 Jacobian is trivial.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

namespace JacobianData

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]

/-- If the degree-zero Picard group of `C` at the test `T` is the trivial subgroup, then
`T` has at most one morphism to the representing object.  Transport of `homEquiv` across
`Equiv.subsingleton`. -/
theorem subsingleton_hom_of_pic0Subgroup_eq_bot (d : JacobianData C) {T : Over (Spec (.of k))}
    (h : pic0Subgroup C T = ⊥) : Subsingleton (T ⟶ d.J) := by
  haveI : Subsingleton (pic0Subgroup C T) := by rw [h]; infer_instance
  exact Equiv.subsingleton d.homEquiv

/-- **The genus-zero reduction.**  If `Pic⁰_{C/k}(T)` is trivial for *every* test object
`T`, then the representing object `d.J` is terminal in `Over (Spec k)`.

Existence of a morphism `T ⟶ d.J` is `homEquiv.symm 1` (the trivial class always exists,
so the `Hom`-set is never empty); uniqueness is
`subsingleton_hom_of_pic0Subgroup_eq_bot`.  Together they are exactly `IsTerminal`.

This carries no genus hypothesis: it is the statement that a functor with trivial values
is represented by a terminal object.  The curve-theoretic input `genus C = 0 →
pic0Subgroup C T = ⊥` is the caller's obligation and is not proved anywhere in this
tree. -/
noncomputable def isTerminal_of_pic0Subgroup_eq_bot (d : JacobianData C)
    (h : ∀ T : Over (Spec (.of k)), pic0Subgroup C T = ⊥) : IsTerminal d.J :=
  IsTerminal.ofUniqueHom (fun _ => d.homEquiv.symm 1)
    (fun T f => (subsingleton_hom_of_pic0Subgroup_eq_bot d (h T)).elim f _)

/-- An `Over`-morphism is an epimorphism as soon as its underlying scheme morphism is:
epi-ness in `Over S` is tested on the left components. -/
theorem epi_of_epi_left {X Y : Over (Spec (.of k))} (u : X ⟶ Y) (h : Epi u.left) :
    Epi u := by
  refine ⟨fun {Z} a b hab => ?_⟩
  ext
  exact (cancel_epi u.left).mp (congrArg Over.Hom.left hab)

/-- The structure morphism of a **terminal** object of `Over (Spec k)` is an isomorphism:
a terminal object is canonically the base itself (`Over.mkIdTerminal`), and transporting
the identity along that iso gives `IsIso J.hom`. -/
theorem isIso_hom_of_isTerminal {J : Over (Spec (.of k))} (hJ : IsTerminal J) :
    IsIso J.hom := by
  have e : J ≅ Over.mk (𝟙 (Spec (.of k))) := hJ.uniqueUpToIso Over.mkIdTerminal
  have hwJ : e.hom.left ≫ (Over.mk (𝟙 (Spec (.of k)))).hom = J.hom := Over.w e.hom
  haveI : IsIso e.hom.left := ((Over.forget _).mapIso e).isIso_hom
  haveI : IsIso (Over.mk (𝟙 (Spec (.of k)))).hom := by
    change IsIso (𝟙 (Spec (.of k))); infer_instance
  rw [← hwJ]; infer_instance

/-- **Any morphism into a terminal object of `Over (Spec k)` out of a surjective source
is an epimorphism.**  This is what discharges the `Epi` hypothesis of
`existsUnique_ofCurve_comp_of_epi` in the degenerate case, with no hand-waving:

* `J` terminal makes `J.hom` an isomorphism (`isIso_hom_of_isTerminal`);
* the triangle `u.left ≫ J.hom = X.hom` (`Over.w`) then transfers both `Surjective`
  and `Flat` from `X.hom` to `u.left`, since both properties cancel on the right
  against an isomorphism;
* every morphism to `Spec` of a field is flat, so `X.hom` supplies flatness for free
  and the only genuine input is surjectivity of `X.hom` — i.e. `X` is nonempty.

Flat + surjective is epi (`Flat.epi_of_flat_of_surjective`), and epi on the left
component is epi in `Over` (`epi_of_epi_left`). -/
theorem epi_of_isTerminal_of_surjective {X J : Over (Spec (.of k))} (hJ : IsTerminal J)
    (u : X ⟶ J) (hs : Surjective X.hom) : Epi u := by
  haveI : IsIso J.hom := isIso_hom_of_isTerminal hJ
  have hw : u.left ≫ J.hom = X.hom := Over.w u
  haveI : Surjective u.left := by
    rw [← MorphismProperty.cancel_right_of_respectsIso (@Surjective) u.left J.hom, hw]
    exact hs
  haveI : Flat u.left := by
    have hf : Flat X.hom := inferInstance
    rw [← MorphismProperty.cancel_right_of_respectsIso (@Flat) u.left J.hom, hw]
    exact hf
  exact epi_of_epi_left u (Flat.epi_of_flat_of_surjective _)

/-- **The Albanese `∃!` when the Abel–Jacobi map is epi.**

Uniqueness of the factorisation is `cancel_epi`, and nothing else: the geometric input
is entirely inside `Epi (d.ofCurve P)`.  For the genus-zero Jacobian that hypothesis is
cheap — `d.J` is then the base `Spec k`, `d.ofCurve P` is the structure morphism of a
nonempty `k`-scheme, and every morphism to `Spec` of a field is flat, so
`Flat.epi_of_flat_of_surjective` (via `epi_of_surjective_left`) supplies it from
surjectivity alone.

The existence hypothesis `hex` is *not* removable and is not hidden: a morphism
`g : d.J ⟶ A` out of a terminal `d.J` is a point of `A`, and `f` factors through
`ofCurve P` exactly when `f` is constant.  Over a genus-0 curve that constancy is what
Milne I 3.9 supplies.  What this lemma records is that the *uniqueness* clause — the
half the frozen target and the descent lane both need — costs nothing beyond `Epi`. -/
theorem existsUnique_ofCurve_comp_of_epi (d : JacobianData C)
    (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) [Epi (d.ofCurve P)] {A : Over (Spec (.of k))}
    (f : C ⟶ A) (hex : ∃ g : d.J ⟶ A, f = d.ofCurve P ≫ g) :
    ∃! g : d.J ⟶ A, f = d.ofCurve P ≫ g := by
  obtain ⟨g, hg⟩ := hex
  refine ⟨g, hg, fun g' hg' => ?_⟩
  apply (cancel_epi (d.ofCurve P)).mp
  rw [← hg, ← hg']

/-- **S11 assembled: the Albanese `∃!` for a degenerate Jacobian.**

From vanishing `Pic⁰` on all tests plus a nonempty curve, the `uniqueness` clause of
the frozen `exists_unique_ofCurve_comp` is fully discharged — no genus hypothesis, no
`ℙ¹`, no rational maps.  Only existence remains, and it is the explicit `hex`.

Chain: `isTerminal_of_pic0Subgroup_eq_bot` → `epi_of_isTerminal_of_surjective` →
`existsUnique_ofCurve_comp_of_epi`. -/
theorem existsUnique_ofCurve_comp_of_pic0Subgroup_eq_bot (d : JacobianData C)
    (h : ∀ T : Over (Spec (.of k)), pic0Subgroup C T = ⊥) (hs : Surjective C.hom)
    (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) {A : Over (Spec (.of k))} (f : C ⟶ A)
    (hex : ∃ g : d.J ⟶ A, f = d.ofCurve P ≫ g) :
    ∃! g : d.J ⟶ A, f = d.ofCurve P ≫ g := by
  haveI : Epi (d.ofCurve P) :=
    epi_of_isTerminal_of_surjective (isTerminal_of_pic0Subgroup_eq_bot d h) _ hs
  exact existsUnique_ofCurve_comp_of_epi d P f hex

/-- In the terminal case the Abel–Jacobi map carries no information: it is *the* unique
morphism `C ⟶ d.J`.  This is the precise content of "the genus-zero Jacobian is
trivial". -/
theorem ofCurve_eq_of_isTerminal (d : JacobianData C) (hJ : IsTerminal d.J)
    (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) (u : C ⟶ d.J) : d.ofCurve P = u :=
  hJ.hom_ext _ _

end JacobianData

end AlgebraicGeometry
