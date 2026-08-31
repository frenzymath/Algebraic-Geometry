/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.FinitePresentation

/-!
# Presented étale covers of an affine base

A (singleton, affine) *étale cover* of `Spec A` is a faithfully flat étale `A`-algebra `B`.
For the étale-sheafification (plus) construction of the relative Picard functor, the covers
of a fixed base must form a *small* directed index: this file realizes them as **presented**
covers — a number of variables `n` together with an ideal of `MvPolynomial (Fin n) A` whose
quotient is étale over `A` with `Spec` mapping onto `Spec A`.  The type of presented covers
of `A` lives in the same universe as `A`, while still capturing every étale cover up to
isomorphism of the carrier (`Algebra.EtaleCover.of` and its accessor `ofEquiv`).

Surjectivity of the spectrum map is recorded instead of faithful flatness because it is
statable without flatness hypotheses; combined with flatness of étale algebras it *is*
faithful flatness (`Module.FaithfullyFlat.of_comap_surjective`), and that instance is
provided on the carrier.

## Main declarations

* `Algebra.EtaleCover A`: presented étale covers of `Spec A`, a `Type u` for `A : Type u`;
  `E.Carrier` is the covering algebra, with `Algebra.Etale A E.Carrier` and
  `Module.FaithfullyFlat A E.Carrier` instances.
* `Algebra.EtaleCover.of B hB`: any étale `A`-algebra `B` (with surjective spectrum map)
  underlies a presented cover, with carrier identification `Algebra.EtaleCover.ofEquiv`.
* `Algebra.EtaleCover.Refines`: `E'` refines `E` when the covering spectrum of `E'` maps
  to that of `E` over the base — a mere existence (`Prop`); the plus construction proves
  independence of the chosen refinement map, so no choice of map is carried here.
* `Algebra.EtaleCover.prod`: the common refinement `Spec (B ⊗[A] B')` of two covers, with
  refinement witnesses `prodInl`/`prodInr` — directedness of the index
  (`exists_refines_prod`).
* `Algebra.EtaleCover.self`: the trivial cover `Spec A` itself, refined by every cover
  (`refines_self`) — the base point of the index.
* `Algebra.EtaleCover.baseChange`: the pulled-back cover along `A → A'`, with carrier
  `A' ⊗[A] E.Carrier` (`baseChangeEquiv`) and the canonical `A`-algebra map
  `baseChangeInclude` into it.
* `Algebra.EtaleCover.exists_finiteSeparableField_algHom`: over a field `K`, every cover
  is refined by a finite separable field extension of `K` (single-factor refinement) —
  field-extension covers are cofinal, the form the degree theory and Galois descent
  consume; `Algebra.EtaleCover.ofField` packages such an extension as a cover.
-/

set_option autoImplicit false

universe u

open TensorProduct

namespace Algebra

/-- A presented étale cover of `Spec A`: a finite-variable polynomial presentation of an
étale `A`-algebra whose spectrum maps onto `Spec A`.  Presentations keep the type of covers
small (`Type u` for `A : Type u`), which is what makes the étale plus construction over
these covers a legitimate colimit; the carrier-level content is recovered by
`Algebra.EtaleCover.of`/`ofEquiv`. -/
structure EtaleCover (A : Type u) [CommRing A] : Type u where
  /-- The number of variables of the presentation. -/
  n : ℕ
  /-- The ideal of relations of the presentation. -/
  ideal : Ideal (MvPolynomial (Fin n) A)
  /-- The presented algebra is étale over the base. -/
  etale : Algebra.Etale A (MvPolynomial (Fin n) A ⧸ ideal)
  /-- The spectrum of the presented algebra covers the spectrum of the base. -/
  comap_surjective :
    Function.Surjective (PrimeSpectrum.comap (algebraMap A (MvPolynomial (Fin n) A ⧸ ideal)))

namespace EtaleCover

variable {A : Type u} [CommRing A]

/-- The covering algebra presented by an étale cover. -/
protected abbrev Carrier (E : EtaleCover A) : Type u :=
  MvPolynomial (Fin E.n) A ⧸ E.ideal

instance (E : EtaleCover A) : Algebra.Etale A E.Carrier :=
  E.etale

instance (E : EtaleCover A) : Module.FaithfullyFlat A E.Carrier :=
  .of_comap_surjective E.comap_surjective

/-! ## Constructors -/

section constructors

variable {B : Type u} [CommRing B] [Algebra A B] [Algebra.Etale A B]

/-- Package an explicitly presented étale algebra with surjective spectrum map as a
presented étale cover: the ideal of relations is the kernel of the presenting
surjection. -/
noncomputable def ofSurjective
    (hB : Function.Surjective (PrimeSpectrum.comap (algebraMap A B)))
    {n : ℕ} (f : MvPolynomial (Fin n) A →ₐ[A] B) (hf : Function.Surjective f) :
    EtaleCover A where
  n := n
  ideal := RingHom.ker f
  etale := .of_equiv (Ideal.quotientKerAlgEquivOfSurjective hf).symm
  comap_surjective := by
    haveI : Module.FaithfullyFlat A B := .of_comap_surjective hB
    haveI : Module.FaithfullyFlat A (MvPolynomial (Fin n) A ⧸ RingHom.ker f) :=
      .of_linearEquiv A B (Ideal.quotientKerAlgEquivOfSurjective hf).toLinearEquiv
    exact PrimeSpectrum.comap_surjective_of_faithfullyFlat

/-- The carrier of `ofSurjective` is the presented algebra. -/
noncomputable def ofSurjectiveEquiv
    (hB : Function.Surjective (PrimeSpectrum.comap (algebraMap A B)))
    {n : ℕ} (f : MvPolynomial (Fin n) A →ₐ[A] B) (hf : Function.Surjective f) :
    (ofSurjective hB f hf).Carrier ≃ₐ[A] B :=
  Ideal.quotientKerAlgEquivOfSurjective hf

/-- Any étale `A`-algebra whose spectrum covers `Spec A` underlies a presented étale
cover.  The presentation is chosen (étale algebras are finitely presented, in particular
finitely generated); the choice is harmless because consumers only ever use the carrier
identification `ofEquiv`. -/
noncomputable def of (B : Type u) [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (hB : Function.Surjective (PrimeSpectrum.comap (algebraMap A B))) : EtaleCover A :=
  ofSurjective hB
    (Algebra.FiniteType.iff_quotient_mvPolynomial''.mp inferInstance).choose_spec.choose
    (Algebra.FiniteType.iff_quotient_mvPolynomial''.mp inferInstance).choose_spec.choose_spec

/-- The carrier of `of B hB` is `B` itself. -/
noncomputable def ofEquiv (B : Type u) [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (hB : Function.Surjective (PrimeSpectrum.comap (algebraMap A B))) :
    (of B hB).Carrier ≃ₐ[A] B :=
  ofSurjectiveEquiv hB _ _

end constructors

/-! ## Refinement and directedness -/

/-- `E'` refines `E`: the covering spectrum of `E'` maps to that of `E` over `Spec A`,
i.e. there is an `A`-algebra map from the carrier of `E` to that of `E'`.  This is a mere
existence: the plus construction proves that the induced maps on descent classes do not
depend on the chosen refinement map, so no map is carried here. -/
def Refines (E' E : EtaleCover A) : Prop :=
  Nonempty (E.Carrier →ₐ[A] E'.Carrier)

theorem refines_refl (E : EtaleCover A) : E.Refines E :=
  ⟨AlgHom.id A E.Carrier⟩

theorem Refines.trans {E E' E'' : EtaleCover A} (h : E''.Refines E') (h' : E'.Refines E) :
    E''.Refines E := by
  obtain ⟨f⟩ := h
  obtain ⟨g⟩ := h'
  exact ⟨f.comp g⟩

/-- The common refinement of two covers: `Spec` of the tensor product of the carriers,
i.e. the fiber product of the covering spectra over the base. -/
noncomputable def prod (E E' : EtaleCover A) : EtaleCover A :=
  haveI : Algebra.Etale A (E.Carrier ⊗[A] E'.Carrier) :=
    Algebra.Etale.comp A E.Carrier (E.Carrier ⊗[A] E'.Carrier)
  haveI : Module.FaithfullyFlat A (E.Carrier ⊗[A] E'.Carrier) :=
    Module.FaithfullyFlat.trans A E.Carrier (E.Carrier ⊗[A] E'.Carrier)
  .of (E.Carrier ⊗[A] E'.Carrier) PrimeSpectrum.comap_surjective_of_faithfullyFlat

/-- The carrier of the common refinement is the tensor product of the carriers. -/
noncomputable def prodEquiv (E E' : EtaleCover A) :
    (E.prod E').Carrier ≃ₐ[A] E.Carrier ⊗[A] E'.Carrier :=
  haveI : Algebra.Etale A (E.Carrier ⊗[A] E'.Carrier) :=
    Algebra.Etale.comp A E.Carrier (E.Carrier ⊗[A] E'.Carrier)
  haveI : Module.FaithfullyFlat A (E.Carrier ⊗[A] E'.Carrier) :=
    Module.FaithfullyFlat.trans A E.Carrier (E.Carrier ⊗[A] E'.Carrier)
  ofEquiv (E.Carrier ⊗[A] E'.Carrier) PrimeSpectrum.comap_surjective_of_faithfullyFlat

/-- The first refinement map of the common refinement. -/
noncomputable def prodInl (E E' : EtaleCover A) : E.Carrier →ₐ[A] (E.prod E').Carrier :=
  ((E.prodEquiv E').symm.toAlgHom).comp Algebra.TensorProduct.includeLeft

/-- The second refinement map of the common refinement. -/
noncomputable def prodInr (E E' : EtaleCover A) : E'.Carrier →ₐ[A] (E.prod E').Carrier :=
  ((E.prodEquiv E').symm.toAlgHom).comp Algebra.TensorProduct.includeRight

/-- Combine refinement maps out of the two factors into one out of the common
refinement (the universal property of the fiber product of the covering spectra). -/
noncomputable def prodLift {E E' F : EtaleCover A} (f : E.Carrier →ₐ[A] F.Carrier)
    (g : E'.Carrier →ₐ[A] F.Carrier) : (E.prod E').Carrier →ₐ[A] F.Carrier :=
  (Algebra.TensorProduct.lift f g fun _ _ => Commute.all _ _).comp
    (E.prodEquiv E').toAlgHom

@[simp]
theorem prodLift_comp_prodInl {E E' F : EtaleCover A} (f : E.Carrier →ₐ[A] F.Carrier)
    (g : E'.Carrier →ₐ[A] F.Carrier) : (prodLift f g).comp (E.prodInl E') = f := by
  ext x
  simp [prodLift, prodInl]

@[simp]
theorem prodLift_comp_prodInr {E E' F : EtaleCover A} (f : E.Carrier →ₐ[A] F.Carrier)
    (g : E'.Carrier →ₐ[A] F.Carrier) : (prodLift f g).comp (E.prodInr E') = g := by
  ext x
  simp [prodLift, prodInr]

theorem prod_refines_left (E E' : EtaleCover A) : (E.prod E').Refines E :=
  ⟨E.prodInl E'⟩

theorem prod_refines_right (E E' : EtaleCover A) : (E.prod E').Refines E' :=
  ⟨E.prodInr E'⟩

/-- Directedness of the refinement preorder: any two covers have a common refinement. -/
theorem exists_refines_prod (E E' : EtaleCover A) :
    ∃ E'' : EtaleCover A, E''.Refines E ∧ E''.Refines E' :=
  ⟨E.prod E', E.prod_refines_left E', E.prod_refines_right E'⟩

/-- The trivial cover of `Spec A` by itself. -/
noncomputable def self (A : Type u) [CommRing A] : EtaleCover A :=
  .of A (by
    rw [show algebraMap A A = RingHom.id A from rfl, PrimeSpectrum.comap_id]
    exact fun p => ⟨p, rfl⟩)

/-- The carrier of the trivial cover is the base ring. -/
noncomputable def selfEquiv (A : Type u) [CommRing A] : (self A).Carrier ≃ₐ[A] A :=
  ofEquiv A _

/-- The canonical refinement map from the trivial cover to any cover (algebra side: the
structure map of the carrier, through the trivial carrier's identification with `A`). -/
noncomputable def fromSelf (E : EtaleCover A) : (self A).Carrier →ₐ[A] E.Carrier :=
  (Algebra.ofId A E.Carrier).comp (selfEquiv A).toAlgHom

/-- Every cover refines the trivial cover: the trivial cover is the base point of the
refinement preorder. -/
theorem refines_self (E : EtaleCover A) : E.Refines (self A) :=
  ⟨E.fromSelf⟩

/-! ## Base change -/

section baseChange

variable (A' : Type u) [CommRing A'] [Algebra A A']

/-- The base change of a cover along `A → A'`: the cover of `Spec A'` with carrier
`A' ⊗[A] E.Carrier` (the fiber product of the covering spectrum with the new base). -/
noncomputable def baseChange (E : EtaleCover A) : EtaleCover A' :=
  .of (A' ⊗[A] E.Carrier) PrimeSpectrum.comap_surjective_of_faithfullyFlat

/-- The carrier of the base-changed cover is the base-changed carrier. -/
noncomputable def baseChangeEquiv (E : EtaleCover A) :
    (E.baseChange A').Carrier ≃ₐ[A'] A' ⊗[A] E.Carrier :=
  ofEquiv (A' ⊗[A] E.Carrier) PrimeSpectrum.comap_surjective_of_faithfullyFlat

/-- The canonical map from the carrier of a cover to the carrier of its base change,
as a map of `A`-algebras. -/
noncomputable def baseChangeInclude (E : EtaleCover A) :
    E.Carrier →ₐ[A] (E.baseChange A').Carrier :=
  (((E.baseChangeEquiv A').symm.toAlgHom).restrictScalars A).comp
    Algebra.TensorProduct.includeRight

/-- The base change of a refinement map: `A' ⊗[A] —` on carriers, through the
presented-carrier identifications — the functoriality of `baseChange` in the cover. -/
noncomputable def baseChangeMap {E F : EtaleCover A} (h : E.Carrier →ₐ[A] F.Carrier) :
    (E.baseChange A').Carrier →ₐ[A'] (F.baseChange A').Carrier :=
  ((F.baseChangeEquiv A').symm.toAlgHom).comp
    ((Algebra.TensorProduct.map (AlgHom.id A' A') h).comp (E.baseChangeEquiv A').toAlgHom)

/-- Base change of refinement maps commutes with the canonical inclusions into the base
change. -/
theorem baseChangeMap_comp_baseChangeInclude {E F : EtaleCover A}
    (h : E.Carrier →ₐ[A] F.Carrier) :
    ((baseChangeMap A' h).restrictScalars A).comp (E.baseChangeInclude A')
      = (F.baseChangeInclude A').comp h := by
  ext x
  simp [baseChangeMap, baseChangeInclude]

end baseChange

/-! ## Covers of a field: single-factor refinement -/

section field

variable {K : Type u} [Field K]

/-- The carrier of a cover of a field (indeed, of any nontrivial base) is nontrivial. -/
theorem nontrivial_carrier (E : EtaleCover A) [Nontrivial A] : Nontrivial E.Carrier :=
  PrimeSpectrum.nonempty_iff_nontrivial.mp
    ⟨(E.comap_surjective (Nonempty.some inferInstance)).choose⟩

/-- **Field cofinality**: over a field, every presented étale cover is refined by a finite
separable field extension.  This single-factor refinement is what makes field-extension
covers cofinal among étale covers of `Spec K`: the étale carrier is a finite product of
finite separable extensions of `K`, and projection to any one factor still covers the
(one-point) spectrum of `K`. -/
theorem exists_finiteSeparableField_algHom (E : EtaleCover K) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : Module.Finite K L)
      (_ : Algebra.IsSeparable K L), Nonempty (E.Carrier →ₐ[K] L) := by
  haveI : Nontrivial E.Carrier := E.nontrivial_carrier
  obtain ⟨I, hI, Ai, hfield, halg, e, h⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod K E.Carrier).mp inferInstance
  haveI : Nonempty I := by
    by_contra hempty
    haveI : IsEmpty I := not_nonempty_iff.mp hempty
    haveI : Subsingleton E.Carrier := e.toEquiv.subsingleton_congr.mpr inferInstance
    exact false_of_nontrivial_of_subsingleton E.Carrier
  obtain ⟨i⟩ := ‹Nonempty I›
  exact ⟨Ai i, hfield i, halg i, (h i).1, (h i).2,
    ⟨(Pi.evalAlgHom K Ai i).comp e.toAlgHom⟩⟩

variable (L : Type u) [Field L] [Algebra K L] [Module.Finite K L] [Algebra.IsSeparable K L]

instance : Algebra.Etale K L where
  formallyEtale := Algebra.FormallyEtale.of_isSeparable K L
  finitePresentation :=
    (Algebra.FinitePresentation.of_finiteType (R := K) (A := L)).mp inferInstance

/-- A finite separable field extension as an étale cover of `Spec K` (the spectrum map
between the one-point spectra is trivially surjective). -/
noncomputable def ofField : EtaleCover K :=
  .of L fun _ => ⟨default, Subsingleton.elim _ _⟩

/-- The carrier of the field cover is the field extension itself. -/
noncomputable def ofFieldEquiv : (ofField (K := K) L).Carrier ≃ₐ[K] L :=
  ofEquiv L _

end field

end EtaleCover

end Algebra
