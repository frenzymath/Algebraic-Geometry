/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Curve.SeparablyClosedFibre

/-!
# Rational points of a smooth curve over a separably closed field (DAT-P)

The density brick **DAT-P** of the Wave-4 DATUM campaign (`informal/w4-datum-worksheet.md` §4
DAT-P, §5 risk 4). Over a **separably closed** field `K`, the `K`-rational points of a scheme
smooth of relative dimension `1` over `K` are dense: every nonempty open contains one.

## Why smoothness is essential (and closed points are not enough)

Over an imperfect separably closed field `K` (e.g. a separable closure of `𝔽ₚ(t)`) not every
closed point is `K`-rational: `𝔸¹_K` has closed points with residue field `K(a^{1/p})`. So the
algebraically-closed argument (`AlgebraicGeometry.pointEquivClosedPoint`, "every closed point is
rational") **fails**. What survives is density of `K`-points, via the standard-smooth chart:

* a standard-smooth chart of relative dimension `1` is étale over the affine line `𝔸¹`;
* over the **infinite** field `K` a `K`-rational base point of `𝔸¹` lies under the chart;
* the fibre there is a finite separable, indeed étale, `K`-algebra, which over the separably
  closed `K` splits into copies of `K` — giving the rational point.

The commutative-algebra core is `AlgebraicJacobian.Curve.SeparablyClosedFibre`
(`AlgebraicGeometry.SeparablyClosed.exists_algHom_of_etale_mvPoly`); this file glues it to the
scheme-level chart machinery of `SmoothOfRelativeDimension 1`.

## Main results (`AlgebraicGeometry.SeparablyClosed`)

* `exists_rationalPoint_of_smoothOfRelativeDimension_one` — a **nonempty** scheme smooth of
  relative dimension `1` over a separably closed field `K` has a `K`-point `Spec K ⟶ X` over `K`.
* `exists_rationalPoint_mem` — **the keystone (density form).** For `f : X ⟶ Spec K` smooth of
  relative dimension `1` over a separably closed `K` and any nonempty open `W` of `X`, there is a
  `K`-point `p : Spec K ⟶ X` over `K` whose topological image lies in `W`. Instantiates at any
  separably closed field of the standing curve pack (`[SmoothOfRelativeDimension 1 C.hom]`) with
  the open given as a nonempty open of the underlying space; consumed by DAT-B's coverage argument
  (the P4(c) `h⁰`-drop with points at `kˢ`-levels).
* `Over.exists_rationalPoint_mem` — the same, phrased for the standing pack `C : Over (Spec K)`.
-/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial
open scoped TensorProduct

namespace AlgebraicGeometry.SeparablyClosed

/-- **A nonempty smooth curve over a separably closed field has a rational point.** For a scheme
`X` smooth of relative dimension `1` over a separably closed field `K`, if `X` is nonempty there is
a `K`-point `p : Spec K ⟶ X` over `K` (`p ≫ f = 𝟙`).

Proof: a standard-smooth chart `V ∋ x₀` of relative dimension `1` gives, via
`RingHom.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial` and transport across
`Γ(Spec K, ⊤) ≅ K`, an étale `K[X]`-algebra structure on `Γ(X, V)`; the commutative-algebra core
`exists_algHom_of_etale_mvPoly` yields a `K`-point `φ : Γ(X, V) →ₐ[K] K`, which `IsAffineOpen`
machinery (`SpecMap_appLE_fromSpec`, `fromSpec_top`) turns into a `K`-point of `X` over `K`. -/
theorem exists_rationalPoint_of_smoothOfRelativeDimension_one {K : Type u} [Field K]
    [IsSepClosed K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
    [Nonempty X] :
    ∃ p : Spec (.of K) ⟶ X, p ≫ f = 𝟙 (Spec (.of K)) := by
  obtain ⟨x₀⟩ := ‹Nonempty X›
  obtain ⟨U, hU, V, hV, hx₀V, e, hsm⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := 1) (f := f) x₀
  have hUtop : U = ⊤ := by
    have hmem : f.base x₀ ∈ U := e hx₀V
    ext y; simpa using Subsingleton.elim (f.base x₀) y ▸ hmem
  subst hUtop
  obtain ⟨g₀, hg₀C, hg₀E⟩ := hsm.exists_etale_mvPolynomial
  letI e_K : Γ(Spec (CommRingCat.of K), ⊤) ≃+* K :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
  let g : MvPolynomial (Fin 1) K →+* Γ(X, V) :=
    g₀.comp (MvPolynomial.mapEquiv (Fin 1) e_K.symm).toRingHom
  have hgE : g.Etale :=
    RingHom.Etale.stableUnderComposition _ _
      (RingHom.Etale.of_bijective (MvPolynomial.mapEquiv (Fin 1) e_K.symm).bijective) hg₀E
  letI algMP : Algebra (MvPolynomial (Fin 1) K) Γ(X, V) := g.toAlgebra
  letI algK : Algebra K Γ(X, V) := (g.comp (MvPolynomial.C)).toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin 1) K) Γ(X, V) := by
    rw [← RingHom.etale_algebraMap]; rwa [RingHom.algebraMap_toAlgebra]
  haveI : IsScalarTower K (MvPolynomial (Fin 1) K) Γ(X, V) := by
    apply IsScalarTower.of_algebraMap_eq'
    rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]; rfl
  haveI : Nontrivial Γ(X, V) := PrimeSpectrum.nontrivial (hV.primeIdealOf ⟨x₀, hx₀V⟩)
  obtain ⟨φ⟩ := SeparablyClosed.exists_algHom_of_etale_mvPoly (K := K) (S := Γ(X, V))
  -- `(map e_K.symm) ∘ C = C ∘ e_K.symm`, hence the `K`-structure map factors the chart map
  have hCmap : (MvPolynomial.mapEquiv (Fin 1) e_K.symm).toRingHom.comp (MvPolynomial.C) =
      (MvPolynomial.C).comp e_K.symm.toRingHom := by
    ext a
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      MvPolynomial.mapEquiv_apply, MvPolynomial.map_C]
  have hI : (algebraMap K Γ(X, V)) = (f.appLE ⊤ V e).hom.comp e_K.symm.toRingHom := by
    rw [RingHom.algebraMap_toAlgebra]
    change (g₀.comp (MvPolynomial.mapEquiv (Fin 1) e_K.symm).toRingHom).comp MvPolynomial.C =
      (f.appLE ⊤ V e).hom.comp e_K.symm.toRingHom
    rw [RingHom.comp_assoc, hCmap, ← RingHom.comp_assoc, hg₀C]
  -- the chart map post-composed with the `K`-point is the canonical iso `Γ(Spec K, ⊤) → K`
  have hring : (f.appLE ⊤ V e) ≫ CommRingCat.ofHom φ.toRingHom =
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom := by
    apply CommRingCat.hom_ext
    have hφ : φ.toRingHom.comp (algebraMap K Γ(X, V)) = RingHom.id K := by
      ext a; exact φ.commutes a
    rw [hI, ← RingHom.comp_assoc] at hφ
    have hthis := congrArg (fun r => r.comp e_K.toRingHom) hφ
    simp only [RingHom.comp_assoc, RingEquiv.toRingHom_eq_coe, RingEquiv.symm_comp,
      RingHom.comp_id, RingHom.id_comp] at hthis
    rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
    exact hthis
  refine ⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ hV.fromSpec, ?_⟩
  calc (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ hV.fromSpec) ≫ f
      = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (hV.fromSpec ≫ f) := by rw [Category.assoc]
    _ = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
          (Spec.map (f.appLE ⊤ V e) ≫ hU.fromSpec) := by
        rw [IsAffineOpen.SpecMap_appLE_fromSpec f hU hV e]
    _ = Spec.map ((f.appLE ⊤ V e) ≫ CommRingCat.ofHom φ.toRingHom) ≫ hU.fromSpec := by
        rw [← Spec.map_comp_assoc]
    _ = Spec.map ((Scheme.ΓSpecIso (CommRingCat.of K)).hom) ≫ hU.fromSpec := by rw [hring]
    _ = (Spec (CommRingCat.of K)).toSpecΓ ≫ hU.fromSpec := by rw [SpecMap_ΓSpecIso_hom]
    _ = 𝟙 (Spec (CommRingCat.of K)) := by
        rw [show hU.fromSpec = (Spec (CommRingCat.of K)).isoSpec.inv from
          IsAffineOpen.fromSpec_top]
        exact Scheme.toSpecΓ_isoSpec_inv _

/-- **DAT-P keystone (density form).** For a scheme `X` smooth of relative dimension `1` over a
separably closed field `K` and any nonempty open `W ⊆ X`, there is a `K`-rational point
`p : Spec K ⟶ X` over `K` whose topological image lies in `W`.

Instantiate at any separably closed field of the standing curve pack by taking `f := C.hom`
(`[SmoothOfRelativeDimension 1 C.hom]`); the open `W` is a nonempty open of the underlying space.
Consumed by DAT-B's coverage argument (the P4(c) `h⁰`-drop with points at `kˢ`-levels). -/
theorem exists_rationalPoint_mem {K : Type u} [Field K] [IsSepClosed K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f] (W : X.Opens)
    (hW : (W : Set X).Nonempty) :
    ∃ p : Spec (.of K) ⟶ X, p ≫ f = 𝟙 (Spec (.of K)) ∧
      p.base (IsLocalRing.closedPoint K) ∈ W := by
  haveI : SmoothOfRelativeDimension 1 (W.ι ≫ f) := IsZariskiLocalAtSource.comp ‹_› W.ι
  haveI : Nonempty W.toScheme := by obtain ⟨x, hx⟩ := hW; exact ⟨⟨x, hx⟩⟩
  obtain ⟨p', hp'⟩ := exists_rationalPoint_of_smoothOfRelativeDimension_one (W.ι ≫ f)
  refine ⟨p' ≫ W.ι, ?_, ?_⟩
  · rw [Category.assoc]; exact hp'
  · simpa using (p'.base (IsLocalRing.closedPoint K)).2

end AlgebraicGeometry.SeparablyClosed

namespace AlgebraicGeometry.Over

variable {K : Type u} [Field K]

/-- **DAT-P keystone for the standing curve pack.** For the curve bundle `C : Over (Spec K)` smooth
of relative dimension `1` over a separably closed field `K`, every nonempty open `W` of the
underlying space `C.left` contains a `K`-rational point: a `K`-point `p : Spec K ⟶ C.left` over
`K` whose topological image lies in `W`. -/
theorem exists_rationalPoint_mem [IsSepClosed K] (C : Over (Spec (.of K)))
    [SmoothOfRelativeDimension 1 C.hom] (W : C.left.Opens) (hW : (W : Set C.left).Nonempty) :
    ∃ p : Spec (.of K) ⟶ C.left, p ≫ C.hom = 𝟙 (Spec (.of K)) ∧
      p.base (IsLocalRing.closedPoint K) ∈ W :=
  SeparablyClosed.exists_rationalPoint_mem C.hom W hW

end AlgebraicGeometry.Over
