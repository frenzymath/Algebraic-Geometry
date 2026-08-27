/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import AlgebraicJacobian.RiemannRoch.Adelic.P1BaseCase
import AlgebraicJacobian.Albanese.CoheightBridge

/-!
# Finiteness of morphisms from the curve to ℙ¹ (node `N9` discharge)

This file discharges the finite-map gate `Adelic.HasFiniteMapToP1` (node `N9`,
`P1BaseCase.lean`) down to a single, strictly weaker gate: the existence of a
*nonconstant* `k`-morphism `C ⟶ ℙ¹_k` (`Adelic.ExistsNonconstantMapToP1`).
Everything between "nonconstant morphism" and "finite morphism" is **proved**:

* **(dim) `Adelic.ringKrullDim_le_one_of_isStandardSmoothOfRelativeDimension_one`** —
  the curve has Krull dimension `≤ 1`: for a standard-smooth algebra `S` of
  relative dimension `1` over a field `k` and a prime `q ⊆ S`, the localisation
  `S_q` has `ringKrullDim ≤ 1`.  The route is unramified-quasi-finite descent to
  `k[X]`: `Ω[S⁄k]` is free of rank one, spanned by exact differentials, so some
  `d t` is an `a • basis` with `a ∉ q`; over `S_q` the element `a` is a unit, so
  `Ω[S_q⁄k]` is spanned by `d t`, hence `Ω[S_q⁄k[X]] = 0` for `X ↦ t` and `S_q`
  is formally unramified and essentially of finite type — hence **quasi-finite**
  — over the PID `k[X]`; incomparability of primes in quasi-finite algebras
  (`Algebra.QuasiFinite.eq_of_le_of_under_eq`) then bounds `dim S_q` by
  `dim k[X] = 1`.
* **(coheight) `Adelic.coheight_le_one_of_curve`** — via the project's
  coheight/stalk bridge (`Scheme.ringKrullDim_stalk_eq_coheight`,
  `Albanese/CoheightBridge.lean`), every point of the curve has topological
  coheight `≤ 1`; in particular every non-generic point is **closed**
  (`Adelic.isClosed_singleton_of_coheight_le_one`).
* **(fibres) `Adelic.finite_of_isClosed_of_ne_univ`,
  `Adelic.finite_preimage_singleton_of_exists_ne`** — on the irreducible
  Noetherian sober curve, closed sets `≠ univ` are finite (their irreducible
  components are singletons), so a *nonconstant* morphism `π` has finite fibres:
  fibres over closed points are proper closed subsets, and fibres over
  non-closed points avoid all closed points of `C` (closed points map to closed
  points, `Scheme.Hom.closePoints_subset_preimage_closedPoints`), hence lie in
  `{generic point}`.
* **(finiteness) `Adelic.isFinite_left_of_exists_ne`** — properness of `π.left`
  by cancellation (`IsProper.of_comp`, target separated), local
  quasi-finiteness from the finite fibres
  (`LocallyQuasiFinite.of_finite_preimage_singleton`), and **Zariski's main
  theorem** (`IsFinite.of_isProper_of_locallyQuasiFinite`, mathlib) conclude
  `IsFinite π.left`.
* **(gate) `Adelic.ExistsNonconstantMapToP1`** — the remaining honest gate: a
  nonconstant `k`-morphism `C ⟶ ℙ¹_k` exists (classically: any nonconstant
  rational function, which exists since `k(C)/k` has transcendence degree one).
  The **derived instance** `Adelic.HasFiniteMapToP1` consumes it together with
  the AJC ambient hypotheses (`IsProper`, `SmoothOfRelativeDimension 1`,
  `GeometricallyIrreducible` — implied by `GeometricallyIntegral`).

Blueprint node: `thm:adelic_exists_finiteMorphismToP1`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Adelic

/-! ### Dimension one for standard-smooth algebras of relative dimension one

The Krull-dimension upper bound `dim S_q ≤ 1`.  This is the "curves are
one-dimensional" input; the lower-bound counterpart lives in
`Albanese/StandardSmoothDimension.lean`. -/

section DimensionOne

/-- **Quasi-finite algebras do not raise dimension.**  If `A` is quasi-finite
over `R` then `ringKrullDim A ≤ ringKrullDim R`: by incomparability
(`Algebra.QuasiFinite.eq_of_le_of_under_eq`), the contraction map
`Spec A → Spec R` is strictly monotone, so chains of primes inject. -/
theorem ringKrullDim_le_of_quasiFinite (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] [Algebra.QuasiFinite R A] :
    ringKrullDim A ≤ ringKrullDim R := by
  refine Order.krullDim_le_of_strictMono
    (fun p : PrimeSpectrum A => PrimeSpectrum.comap (algebraMap R A) p) ?_
  intro p p' hlt
  have hle : PrimeSpectrum.comap (algebraMap R A) p ≤
      PrimeSpectrum.comap (algebraMap R A) p' := Ideal.comap_mono hlt.le
  refine lt_of_le_of_ne hle fun heq => hlt.ne ?_
  have h2 : p.asIdeal.under R = p'.asIdeal.under R := congrArg PrimeSpectrum.asIdeal heq
  exact PrimeSpectrum.ext
    (Algebra.QuasiFinite.eq_of_le_of_under_eq (R := R) p.asIdeal p'.asIdeal hlt.le h2)

variable {k : Type u} [Field k] {S : Type u} [CommRing S] [Algebra k S]

/-- **Local dimension `≤ 1` for standard-smooth algebras of relative
dimension one over a field.**  For a prime `q` of `S` and any localisation
`Sq` of `S` at `q`, we have `ringKrullDim Sq ≤ 1`.

Proof sketch: `Ω[S⁄k]` is free of rank one and spanned by exact differentials,
so writing the basis vector as a finite combination `∑ cᵢ • d sᵢ` and reading
off coordinates, some `d t` has coordinate `a ∉ q`.  Over `Sq` the coordinate
`a` becomes a unit, so `d t` spans `Ω[Sq⁄k]`; mapping `X ↦ t` makes `Sq`
formally unramified (`Ω[Sq⁄k[X]] = 0`) and essentially of finite type over
`k[X]`, hence quasi-finite; `ringKrullDim_le_of_quasiFinite` and
`dim k[X] = 1` (PID) conclude. -/
theorem ringKrullDim_le_one_of_isStandardSmoothOfRelativeDimension_one
    [Algebra.IsStandardSmoothOfRelativeDimension 1 k S]
    (q : Ideal S) [hq : q.IsPrime]
    (Sq : Type u) [CommRing Sq] [Algebra S Sq] [Algebra k Sq] [IsScalarTower k S Sq]
    [IsLocalization.AtPrime Sq q] :
    ringKrullDim Sq ≤ 1 := by
  -- `S` is nontrivial since it has a prime ideal.
  haveI : Nontrivial S := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hq.ne_top (q.eq_top_of_isUnit_mem q.zero_mem
      (isUnit_zero_iff.mpr (Subsingleton.elim _ _)))
  haveI : Algebra.IsStandardSmooth k S :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  -- `Ω[S⁄k]` is free of rank one; choose a basis with (necessarily) unique index.
  have hrank : Module.rank S (Ω[S⁄k]) = 1 := by
    exact_mod_cast Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
      (R := k) (S := S) 1
  set ι := Module.Free.ChooseBasisIndex S (Ω[S⁄k]) with hιdef
  let b : Module.Basis ι S (Ω[S⁄k]) := Module.Free.chooseBasis S (Ω[S⁄k])
  have hcard : (Cardinal.mk ι) = 1 := by
    rw [hιdef, ← Module.Free.rank_eq_card_chooseBasisIndex]; exact hrank
  obtain ⟨hsub, ⟨i₀⟩⟩ : Subsingleton ι ∧ Nonempty ι := Cardinal.eq_one_iff_unique.mp hcard
  haveI := hsub
  -- Every element of `Ω[S⁄k]` is its `i₀`-coordinate times the basis vector.
  have hexp : ∀ ω : Ω[S⁄k], ω = b.repr ω i₀ • b i₀ := by
    intro ω
    haveI : Unique ι := uniqueOfSubsingleton i₀
    have h := b.sum_repr ω
    rw [Fintype.sum_unique, Subsingleton.elim (default : ι) i₀] at h
    exact h.symm
  -- The basis vector is a finite combination of exact differentials.
  have hmem : b i₀ ∈ Submodule.span S (Set.range (KaehlerDifferential.D k S)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  obtain ⟨n, c, w, hw⟩ := Submodule.mem_span_set'.mp hmem
  -- Reading off `i₀`-coordinates: the coordinates of the `d sᵢ` generate `1`.
  have hone : (1 : S) = ∑ j, c j * b.repr (w j : Ω[S⁄k]) i₀ := by
    have h := congrArg (fun ω => b.repr ω i₀) hw
    simpa [map_sum, Finset.sum_apply', Finsupp.smul_apply, smul_eq_mul,
      Module.Basis.repr_self, Finsupp.single_eq_same] using h.symm
  -- Some exact differential has coordinate outside `q`.
  have hex : ∃ j, b.repr (w j : Ω[S⁄k]) i₀ ∉ q := by
    by_contra h
    simp only [not_exists, not_not] at h
    have h1 : (1 : S) ∈ q := by
      rw [hone]
      exact Ideal.sum_mem q fun j _ => Ideal.mul_mem_left q _ (h j)
    exact hq.ne_top (q.eq_top_of_isUnit_mem h1 isUnit_one)
  obtain ⟨j, haq⟩ := hex
  obtain ⟨t, ht⟩ : ∃ t, KaehlerDifferential.D k S t = (w j : Ω[S⁄k]) := (w j).2
  set a : S := b.repr (w j : Ω[S⁄k]) i₀ with hadef
  have hDt : KaehlerDifferential.D k S t = a • b i₀ := by rw [ht]; exact hexp _
  -- Transport to the localisation `Sq`; `a` becomes a unit, so `d t` spans.
  haveI : IsLocalizedModule q.primeCompl (KaehlerDifferential.map k k S Sq) :=
    KaehlerDifferential.isLocalizedModule_map k S Sq q.primeCompl
  set b' : Module.Basis ι Sq (Ω[Sq⁄k]) :=
    b.ofIsLocalizedModule Sq q.primeCompl (KaehlerDifferential.map k k S Sq) with hb'def
  set t₁ : Sq := algebraMap S Sq t with ht₁def
  have hDt₁ : KaehlerDifferential.D k Sq t₁ = algebraMap S Sq a • b' i₀ := by
    have h1 : KaehlerDifferential.map k k S Sq (KaehlerDifferential.D k S t)
        = KaehlerDifferential.D k Sq t₁ := KaehlerDifferential.map_D k k S Sq t
    rw [← h1, hDt, map_smul, hb'def, Module.Basis.ofIsLocalizedModule_apply, algebraMap_smul]
  have hunit : IsUnit (algebraMap S Sq a) :=
    IsLocalization.map_units (M := q.primeCompl) Sq ⟨a, haq⟩
  have hspan' : Submodule.span Sq {KaehlerDifferential.D k Sq t₁} = ⊤ := by
    have hb' : Submodule.span Sq (Set.range b') = ⊤ := b'.span_eq
    have hr : Set.range b' = {b' i₀} := by
      ext ω
      constructor
      · rintro ⟨i, rfl⟩
        rw [Subsingleton.elim i i₀]
        exact Set.mem_singleton _
      · rintro rfl
        exact ⟨i₀, rfl⟩
    rw [hDt₁, Submodule.span_singleton_smul_eq hunit]
    rw [hr] at hb'
    exact hb'
  -- `Sq` is a `k[X]`-algebra via `X ↦ t₁`, formally unramified since `d t₁` spans.
  letI : Algebra (Polynomial k) Sq := (Polynomial.aeval t₁).toRingHom.toAlgebra
  haveI : IsScalarTower k (Polynomial k) Sq := IsScalarTower.of_algebraMap_eq fun r => by
    rw [RingHom.algebraMap_toAlgebra]
    exact ((Polynomial.aeval t₁).commutes r).symm
  haveI : Algebra.FormallyUnramified (Polynomial k) Sq := by
    refine ⟨?_⟩
    have hsurj : Function.Surjective (KaehlerDifferential.map k (Polynomial k) Sq Sq) :=
      KaehlerDifferential.map_surjective k (Polynomial k) Sq
    have hker : KaehlerDifferential.map k (Polynomial k) Sq Sq
        (KaehlerDifferential.D k Sq t₁) = 0 := by
      rw [KaehlerDifferential.map_D]
      have hX : algebraMap Sq Sq t₁ = algebraMap (Polynomial k) Sq Polynomial.X := by
        have h1 : algebraMap (Polynomial k) Sq Polynomial.X = t₁ := by
          rw [RingHom.algebraMap_toAlgebra]
          exact Polynomial.aeval_X t₁
        rw [h1, Algebra.algebraMap_self, RingHom.id_apply]
      rw [hX, Derivation.map_algebraMap]
    refine subsingleton_of_forall_eq 0 fun ω' => ?_
    obtain ⟨ω, rfl⟩ := hsurj ω'
    have hω : ω ∈ Submodule.span Sq {KaehlerDifferential.D k Sq t₁} := by
      rw [hspan']; exact Submodule.mem_top
    obtain ⟨c', rfl⟩ := Submodule.mem_span_singleton.mp hω
    rw [map_smul, hker, smul_zero]
  -- `Sq` is essentially of finite type over `k[X]`.
  haveI : Algebra.EssFiniteType k S := Algebra.EssFiniteType.of_finiteType k S
  haveI : Algebra.EssFiniteType S Sq := Algebra.EssFiniteType.of_isLocalization Sq q.primeCompl
  haveI : Algebra.EssFiniteType k Sq := Algebra.EssFiniteType.comp k S Sq
  haveI : Algebra.EssFiniteType (Polynomial k) Sq :=
    Algebra.EssFiniteType.of_comp k (Polynomial k) Sq
  -- Unramified + essentially of finite type ⟹ quasi-finite over the PID `k[X]`.
  haveI : Algebra.QuasiFinite (Polynomial k) Sq := inferInstance
  have hk : ringKrullDim (Polynomial k) ≤ 1 := by
    exact_mod_cast Ring.krullDimLE_iff.mp
      (inferInstance : Ring.KrullDimLE 1 (Polynomial k))
  exact le_trans (ringKrullDim_le_of_quasiFinite (Polynomial k) Sq) hk

end DimensionOne

/-! ### Stalk dimension and coheight of the smooth curve -/

section Coheight

variable {k : Type u} [Field k]

/-- **Stalk dimension `≤ 1` on the AJC curve.**  For a scheme `C` smooth of
relative dimension one over `Spec k`, every stalk has Krull dimension `≤ 1`.
The standard-smooth chart around the point is a standard-smooth
`k`-algebra of relative dimension one (identifying the base sections with `k`
along `Scheme.ΓSpecIso`), and the stalk is its localisation at the prime of
the point (`IsAffineOpen.isLocalization_stalk`). -/
theorem ringKrullDim_stalk_le_one_of_curve (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] (z : C.left) :
    ringKrullDim (C.left.presheaf.stalk z) ≤ 1 := by
  obtain ⟨U, hU, V, hV, hzV, e, hss⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := 1)
      (f := C.hom) z
  -- The base `Spec k` has a single point, so `U = ⊤`.
  haveI : Subsingleton (Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  have hUtop : U = ⊤ := by
    refine top_le_iff.mp fun x _ => ?_
    rw [Subsingleton.elim x (C.hom.base z)]
    exact e hzV
  subst hUtop
  -- Identify the base sections with `k` and transport standard smoothness.
  let eΓ : Γ(Spec (CommRingCat.of k), ⊤) ≃+* k :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  have hφss : RingHom.IsStandardSmoothOfRelativeDimension 1
      ((C.hom.appLE ⊤ V e).hom.comp eΓ.symm.toRingHom) :=
    (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := 1)).right _ eΓ.symm hss
  letI : Algebra k Γ(C.left, V) := ((C.hom.appLE ⊤ V e).hom.comp eΓ.symm.toRingHom).toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 1 k Γ(C.left, V) := hφss.toAlgebra
  -- The stalk is the localisation of the chart ring at the prime of `z`.
  letI : Algebra Γ(C.left, V) (C.left.presheaf.stalk z) :=
    TopCat.Presheaf.algebra_section_stalk C.left.presheaf ⟨z, hzV⟩
  haveI : IsLocalization.AtPrime (C.left.presheaf.stalk z)
      (hV.primeIdealOf ⟨z, hzV⟩).asIdeal := hV.isLocalization_stalk ⟨z, hzV⟩
  letI : Algebra k (C.left.presheaf.stalk z) :=
    ((algebraMap Γ(C.left, V) (C.left.presheaf.stalk z)).comp
      (algebraMap k Γ(C.left, V))).toAlgebra
  haveI : IsScalarTower k Γ(C.left, V) (C.left.presheaf.stalk z) := by
    exact IsScalarTower.of_algebraMap_eq' rfl
  haveI : (hV.primeIdealOf ⟨z, hzV⟩).asIdeal.IsPrime := (hV.primeIdealOf ⟨z, hzV⟩).isPrime
  exact ringKrullDim_le_one_of_isStandardSmoothOfRelativeDimension_one (k := k)
    (hV.primeIdealOf ⟨z, hzV⟩).asIdeal (C.left.presheaf.stalk z)

/-- **Coheight `≤ 1` on the AJC curve.**  Via the project bridge
`Scheme.ringKrullDim_stalk_eq_coheight`. -/
theorem coheight_le_one_of_curve (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] (z : C.left) :
    Order.coheight z ≤ 1 := by
  have h := ringKrullDim_stalk_le_one_of_curve C z
  rw [Scheme.ringKrullDim_stalk_eq_coheight] at h
  exact_mod_cast h

end Coheight

/-! ### Topology: on a one-dimensional irreducible scheme, proper closed
subsets are finite -/

section Topology

/-- On an irreducible scheme whose points all have coheight `≤ 1`, every
non-generic point is closed: a strict specialisation `z' < z < generic` would
force `coheight z' ≥ 2`. -/
theorem isClosed_singleton_of_coheight_le_one {X : Scheme.{u}} [IrreducibleSpace X]
    (hdim : ∀ w : X, Order.coheight w ≤ 1) {z : X} (hz : z ≠ genericPoint X) :
    IsClosed ({z} : Set X) := by
  refine isClosed_of_closure_subset fun z' hz' => ?_
  by_contra hne
  rw [Set.mem_singleton_iff] at hne
  -- Specialisation chain `z' < z < genericPoint X` in the specialisation order.
  have h1 : z ⤳ z' := specializes_iff_mem_closure.mpr hz'
  have h2 : genericPoint X ⤳ z := genericPoint_specializes z
  have hlt1 : z' < z :=
    lt_iff_le_not_ge.mpr ⟨h1, fun h => hne ((show z' ⤳ z from h).antisymm h1).eq⟩
  have hlt2 : z < genericPoint X :=
    lt_iff_le_not_ge.mpr ⟨h2, fun h => hz ((show z ⤳ genericPoint X from h).antisymm h2).eq⟩
  have hc1 : Order.coheight (genericPoint X) + 1 ≤ Order.coheight z :=
    Order.coheight_add_one_le hlt2
  have hc2 : Order.coheight z + 1 ≤ Order.coheight z' := Order.coheight_add_one_le hlt1
  have h1le : (1 : ℕ∞) ≤ Order.coheight z := le_trans le_add_self hc1
  have h2le : (2 : ℕ∞) ≤ Order.coheight z' := by
    refine le_trans ?_ hc2
    rw [show (2 : ℕ∞) = 1 + 1 by norm_num]
    exact add_le_add h1le le_rfl
  exact absurd (show (2 : ℕ) ≤ 1 by exact_mod_cast h2le.trans (hdim z')) (by omega)

/-- **Closed proper subsets of the curve are finite.**  On an irreducible
Noetherian (sober) scheme all of whose points have coheight `≤ 1`, every
closed set `≠ univ` is finite: its finitely many irreducible components have
closed generic points, hence are singletons. -/
theorem finite_of_isClosed_of_ne_univ {X : Scheme.{u}} [IrreducibleSpace X]
    [TopologicalSpace.NoetherianSpace X]
    (hdim : ∀ w : X, Order.coheight w ≤ 1)
    {F : Set X} (hF : IsClosed F) (hFne : F ≠ Set.univ) :
    F.Finite := by
  have hgen : genericPoint X ∉ F := by
    intro h
    refine hFne (Set.eq_univ_of_univ_subset ?_)
    rw [← genericPoint_closure (α := X)]
    exact hF.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr h)
  obtain ⟨T, hTfin, hTclosed, hTirr, hFeq⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hF
  rw [hFeq]
  refine Set.Finite.sUnion hTfin fun t ht => ?_
  obtain ⟨ζ, hζ⟩ := QuasiSober.sober (hTirr t ht) (hTclosed t ht)
  have hζt : ζ ∈ t := hζ.mem
  have hζF : ζ ∈ F := hFeq ▸ Set.mem_sUnion.mpr ⟨t, ht, hζt⟩
  have hζne : ζ ≠ genericPoint X := fun h => hgen (h ▸ hζF)
  have hcl : IsClosed ({ζ} : Set X) := isClosed_singleton_of_coheight_le_one hdim hζne
  have hteq : t = {ζ} := by rw [← hζ]; exact hcl.closure_eq
  rw [hteq]
  exact Set.finite_singleton ζ

end Topology

/-! ### Fibres of a nonconstant morphism from the curve are finite -/

section Fibres

variable {k : Type u} [Field k]

/-- **Fibre finiteness.**  A nonconstant `k`-morphism `π : C ⟶ Y` from the
AJC curve (proper, smooth of relative dimension one, geometrically
irreducible over `k`) to a locally-of-finite-type `k`-scheme `Y` has finite
fibres.  Fibres over closed points are proper closed subsets of the curve,
hence finite; fibres over non-closed points avoid the closed points of `C`
(closed points map to closed points of the Jacobson scheme `Y`), so they lie
inside `{generic point}`. -/
theorem finite_preimage_singleton_of_exists_ne {C Y : Over (Spec (CommRingCat.of k))}
    [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    [LocallyOfFiniteType Y.hom]
    (π : C ⟶ Y) (hπ : ∃ x₁ x₂ : C.left, π.left x₁ ≠ π.left x₂) (y : Y.left) :
    (π.left ⁻¹' {y}).Finite := by
  -- Ambient instances on the curve: irreducible, Noetherian, compact.
  haveI : Smooth C.hom := SmoothOfRelativeDimension.smooth 1 C.hom
  haveI : Subsingleton (Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  haveI : Nonempty (Spec (CommRingCat.of k)) :=
    inferInstanceAs (Nonempty (PrimeSpectrum k))
  haveI : IrreducibleSpace C.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton C.hom
  haveI : IsNoetherianRing (CommRingCat.of k) := inferInstanceAs (IsNoetherianRing k)
  haveI : IsLocallyNoetherian C.left := LocallyOfFiniteType.isLocallyNoetherian C.hom
  haveI : CompactSpace (Spec (CommRingCat.of k)) :=
    inferInstanceAs (CompactSpace (PrimeSpectrum k))
  haveI : CompactSpace C.left := QuasiCompact.compactSpace_of_compactSpace C.hom
  haveI : IsNoetherian C.left := {}
  -- The target is a Jacobson scheme.
  haveI : IsJacobsonRing (CommRingCat.of k) := inferInstanceAs (IsJacobsonRing k)
  haveI : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  -- `π.left` is locally of finite type (cancellation along the structure maps).
  haveI : LocallyOfFiniteType (π.left ≫ Y.hom) := by rw [Over.w π]; infer_instance
  haveI : LocallyOfFiniteType π.left := locallyOfFiniteType_of_comp π.left Y.hom
  have hdim := coheight_le_one_of_curve C
  by_cases hy : IsClosed ({y} : Set Y.left)
  · -- Fibre over a closed point: closed and proper, hence finite.
    refine finite_of_isClosed_of_ne_univ hdim (hy.preimage π.left.continuous) fun h => ?_
    obtain ⟨x₁, x₂, hx⟩ := hπ
    have h₁ : π.left x₁ = y := Set.eq_univ_iff_forall.mp h x₁
    have h₂ : π.left x₂ = y := Set.eq_univ_iff_forall.mp h x₂
    exact hx (h₁.trans h₂.symm)
  · -- Fibre over a non-closed point avoids all closed points of `C`.
    refine Set.Finite.subset (Set.finite_singleton (genericPoint C.left)) fun x hx => ?_
    rw [Set.mem_singleton_iff]
    by_contra hxg
    have hxcl : x ∈ closedPoints C.left :=
      isClosed_singleton_of_coheight_le_one hdim hxg
    have himg : π.left x ∈ closedPoints Y.left :=
      π.left.closePoints_subset_preimage_closedPoints hxcl
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hx
    exact hy (hx ▸ himg)

/-- **Nonconstant morphisms from the curve are finite (nodes `N9b–N9d`).**
For the AJC curve `C` (proper, smooth of relative dimension one,
geometrically irreducible over `k`) and a separated, locally-of-finite-type
`k`-scheme `Y`, any `k`-morphism `π : C ⟶ Y` taking two distinct values is a
finite morphism of schemes:

* `π.left` is **proper**, by cancellation `IsProper.of_comp` applied to
  `π.left ≫ Y.hom = C.hom` (target separated);
* `π.left` is **locally quasi-finite**, by fibre finiteness
  (`finite_preimage_singleton_of_exists_ne`);
* proper + quasi-finite ⟹ finite is **Zariski's main theorem**
  (`IsFinite.of_isProper_of_locallyQuasiFinite`). -/
theorem isFinite_left_of_exists_ne {C Y : Over (Spec (CommRingCat.of k))}
    [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom]
    (π : C ⟶ Y) (hπ : ∃ x₁ x₂ : C.left, π.left x₁ ≠ π.left x₂) :
    IsFinite π.left := by
  haveI : IsProper (π.left ≫ Y.hom) := by rw [Over.w π]; infer_instance
  haveI : IsProper π.left := IsProper.of_comp π.left Y.hom
  haveI : LocallyQuasiFinite π.left :=
    LocallyQuasiFinite.of_finite_preimage_singleton π.left
      (finite_preimage_singleton_of_exists_ne π hπ)
  exact IsFinite.of_isProper_of_locallyQuasiFinite π.left

end Fibres

/-! ### The nonconstant-map gate and the derived `HasFiniteMapToP1` instance -/

section Gate

variable {k : Type u} [Field k]

/-- **The nonconstant-map gate (node `N9a`).**  A single-field `Prop` class
asserting the existence of a `k`-morphism `C ⟶ ℙ¹_k` that takes two distinct
values.  This is the honest remaining kernel of the finite-map gate `N9`: it
is a *Kleiman-independent classical existence statement* (any nonconstant
rational function on the curve — which exists since `k(C)/k` has
transcendence degree one — extends to a morphism to `ℙ¹` by the valuative
property of the dimension-one regular local rings).  Everything from here to
`HasFiniteMapToP1` is proved (`isFinite_left_of_exists_ne` + the derived instance below).

**Update (2026-07-27): the "carries no instance" clause this docstring used to end with
is obsolete.**  `NonconstantToP1.lean` discharges this class for an AJC curve —
`existsNonconstantMapToProjInt_of_ajc` builds the nonconstant map by the two-chart
construction under `[SmoothOfRelativeDimension 1] [IsProper] [GeometricallyIntegral]`,
and `existsNonconstantMapToP1_of_existsNonconstantMapToProjInt` transfers it here — so
under those hypotheses the whole `N9` chain synthesises with no gate left open.  The class
survives for use at generality beyond the AJC curve. -/
class ExistsNonconstantMapToP1 (C : Over (Spec (CommRingCat.of k))) : Prop where
  /-- There exists a `k`-morphism `C ⟶ ℙ¹_k` taking two distinct values. -/
  exists_nonconstant_map :
    ∃ π : C ⟶ Over.mk (ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) ↘
        Spec (CommRingCat.of k)),
      ∃ x₁ x₂ : C.left, π.left x₁ ≠ π.left x₂

/-- **The finite-map gate holds given a nonconstant map (node `N9`
discharge).**  Under the AJC ambient hypotheses (`IsProper`,
`SmoothOfRelativeDimension 1`, `GeometricallyIrreducible` — the latter implied
by `GeometricallyIntegral`), a nonconstant `k`-morphism `C ⟶ ℙ¹_k` is
automatically finite, so the gate `HasFiniteMapToP1` follows from the strictly
weaker gate `ExistsNonconstantMapToP1`. -/
instance (priority := 100) hasFiniteMapToP1_of_existsNonconstantMapToP1
    (C : Over (Spec (CommRingCat.of k)))
    [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    [ExistsNonconstantMapToP1 C] : HasFiniteMapToP1 C := by
  obtain ⟨π, hπ⟩ := ExistsNonconstantMapToP1.exists_nonconstant_map (C := C)
  haveI : IsSeparated (Over.mk (ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) ↘
      Spec (CommRingCat.of k))).hom :=
    inferInstanceAs (IsSeparated (ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) ↘
      Spec (CommRingCat.of k)))
  haveI : IsProper (Over.mk (ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) ↘
      Spec (CommRingCat.of k))).hom :=
    inferInstanceAs (IsProper (ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) ↘
      Spec (CommRingCat.of k)))
  exact ⟨⟨π, isFinite_left_of_exists_ne π hπ⟩⟩

end Gate

end AlgebraicGeometry.Adelic
