/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Picard.FGAPicRepresentability
import AlgebraicJacobian.RiemannRoch.CurveBaseChange

/-!
# Rational points of a smooth curve over a separably closed field, and the `k^s` section

**The root of the Milne–Kollár route.** Every milestone of cluster `J`
(`informal/pic-representability-campaign.md`) runs "over a separably closed field `k'`, where a
section is available": `J1` needs an `(r−g)`-tuple of **rational** points of `C'`, `J4` subtracts
only rational points, `P4(c)/(d)` are pinned separably-closed-only, and
`Picard/PicEtSubcanonical.lean` relies on the section to keep the `G3` refutation from sinking
the route. Until this file, that availability was **asserted at every consuming site and proved
at none**: the project's only rational-point producer is
`hasRationalPoint_of_isAlgClosed` (`Albanese/AlbaneseUP.lean`), which needs `[IsAlgClosed]` —
forbidden here by the route's own char-`p` discipline (campaign `G1`: "`k^s`, **never** `k̄`").

## Why the algebraically closed proof does not transpose

Over an **imperfect** separably closed `K` (a separable closure of `𝔽ₚ(t)`) not every closed
point is `K`-rational: `𝔸¹_K` has closed points with residue field `K(a^{1/p})`. So
`AlgebraicGeometry.pointEquivClosedPoint` — "every closed point is rational", the last step of
the algebraically closed producer — has **no separable analogue**, and weakening that step alone
would be an attempt to prove something false. Smoothness gives separable residue fields for the
*fibre of an étale map*, not at an arbitrary closed point. (Measured: `IsAlgClosed K` yields
`PerfectField K` via `IsAlgClosed.perfectField`, while `IsSepClosed K` does not, so the imperfect
separably closed case is real rather than hypothetical.)

What works instead is the **standard-smooth chart**, and it is why the relative-dimension
numeral is load-bearing rather than decorative:

* a standard-smooth chart of relative dimension `1` is étale over the affine line `𝔸¹`
  (`RingHom.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial`); bare `Smooth`
  yields a chart of unknown relative dimension and the `𝔸¹` step never starts;
* over the **infinite** field `K` (§1, from separable closedness) a `K`-rational base point of
  `𝔸¹` lies under the chart, by Chevalley openness of the image;
* the fibre there is a nonzero étale `K`-algebra, which over separably closed `K` splits into
  copies of `K` (`Algebra.FormallyEtale.equivPiOfIsSepClosed`) — giving the rational point.

## Provenance

§1–§3 are transcribed from the sibling project `Algebraic-Jacobian-Challenge-Rebuild`
(`Curve/SeparablyClosedFibre.lean`, `Curve/SeparablyClosedPoints.lean`, campaign brick `DAT-P`),
which proves them at the same toolchain and the same mathlib revision. The transcription is
faithful rather than adapted: both sibling files import only `Mathlib`, so unlike the `picEt`
cross-project match — where the two projects' objects genuinely differ — there is **no carrier
gap** to bridge. The sibling's conclusion is `∃ p, p ≫ f = 𝟙`, which is
`Scheme.HasRationalPoint`'s field at `f := C.hom` with the existential re-packaged as a
`Nonempty` subtype.

§4 is **not** in the sibling and is the part this project needs: the route does not consume a
bare scheme over a separably closed field, it consumes `Scheme.HasRationalPoint` at the curve
**base-changed to a separable closure of `k`**. That is a separate statement, and it is where the
binder bookkeeping happens.

## Main results

* `AlgebraicGeometry.SeparablyClosed.exists_algHom_of_etale_mvPoly` — §2, the
  commutative-algebra core: a nonzero `K`-algebra étale over `K[X]`, with `K` separably closed,
  has a `K`-point.
* `AlgebraicGeometry.SeparablyClosed.exists_rationalPoint_of_smoothOfRelativeDimension_one` — §3,
  a **nonempty** scheme smooth of relative dimension `1` over separably closed `K` has a
  `K`-point. Note what it does *not* need: no `[IsProper]`, no `[GeometricallyIntegral]`. That is
  strictly weaker than the binder bundle every `J`-milestone carries, so it covers the whole
  cluster.
* `AlgebraicGeometry.SeparablyClosed.exists_rationalPoint_mem` — the density form.
* `AlgebraicGeometry.Scheme.hasRationalPoint_of_isSepClosed` — §4, the class form: the producer
  the route's consumers can actually synthesize against.
* `AlgebraicGeometry.Scheme.hasRationalPoint_baseChangeField_separableClosure` — §4, **the
  bridge**: `C_{k^s}` has a `k^s`-rational point, for `C` a smooth proper geometrically integral
  curve over an *arbitrary* field `k`, with no hypothesis on `C(k)`.

## What this does and does not discharge

**Discharged.** The section at `k^s`, unconditionally on `C(k)`. The specific goal
`Picard/PicEtSubcanonical.lean` had no producer for — `Scheme.HasRationalPoint C` for a curve over
a separably closed field — closes by `Scheme.hasRationalPoint_of_isSepClosed`.

**Not discharged, and both limits were found by auditing this file rather than assumed.**

* Campaign `G1` spreads `J5`'s datum to a **finite** Galois level `k'/k`; `IsSepClosed k'` is false
  at a finite level and nothing here produces a point there. The step from `k^s` to finite levels
  is a separate obligation, unpriced by any site.
* `J1` wants an `(r−g)`-**tuple** of rational points. `exists_rationalPoint_mem` transports to the
  base-changed curve, so points are plentiful by density, but extracting two *distinct* sections
  does not follow from the bridge alone.
* There are as yet **no formal consumers**: cluster `J`'s milestones are campaign prose, not Lean
  binders, and the only citation of this file elsewhere is a docstring.
* `fgaPicardRepresentability` is untouched. The seam sorry is representability of `picEt`; this is
  one input of one branch of one route towards it, and nothing here mentions the Picard functor.
-/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial PrimeSpectrum
open scoped TensorProduct

namespace AlgebraicGeometry.SeparablyClosed

/-! ## §1. A separably closed field is infinite -/

/-- A separably closed field is infinite: `X^{n+1} - 1` is separable when `n+1 ≠ 0` in `K`, so it
splits with `n+1` distinct roots, which a field of cardinality `n` cannot hold. -/
instance (priority := 500) instInfiniteOfIsSepClosed {K : Type u} [Field K] [IsSepClosed K] :
    Infinite K := by
  apply Infinite.of_not_fintype
  intro hfin
  set n := Fintype.card K with hn
  set f : Polynomial K := Polynomial.X ^ (n + 1) - Polynomial.C 1 with hf
  have hfsep : f.Separable := by
    rw [hf]; exact Polynomial.separable_X_pow_sub_C 1 (by simp [hn]) one_ne_zero
  apply Nat.not_succ_le_self (Fintype.card K)
  have hdeg : f.natDegree = n + 1 := by rw [hf, Polynomial.natDegree_X_pow_sub_C]
  have hroot : n.succ = Fintype.card (f.rootSet K) := by
    rw [Polynomial.card_rootSet_eq_natDegree hfsep (IsSepClosed.splits_domain _ hfsep), hdeg]
  rw [hroot]
  exact Fintype.card_le_of_injective _ Subtype.coe_injective

variable {K : Type u} [Field K]

/-! ## §2. The commutative-algebra core -/

/-- The `K`-rational point of `Spec (K[X]) = 𝔸¹` associated to a value `x : Fin 1 → K`:
the prime `ker (aeval x)`, i.e. the maximal ideal `(X - x₀)`. -/
noncomputable def ratPt (x : Fin 1 → K) : PrimeSpectrum (MvPolynomial (Fin 1) K) :=
  PrimeSpectrum.comap (aeval x).toRingHom ⊥

/-- Membership of the rational point `ratPt x` in a basic open `D(h)`: it holds iff `h` does not
vanish at `x`. -/
theorem mem_ratPt_basicOpen (x : Fin 1 → K) (h : MvPolynomial (Fin 1) K) :
    ratPt x ∈ basicOpen h ↔ aeval x h ≠ 0 := by
  rw [PrimeSpectrum.mem_basicOpen]
  simp only [ratPt, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  rw [show ((⊥ : PrimeSpectrum K).asIdeal) = (⊥ : Ideal K) from rfl]
  simp

/-- For a nonzero `K`-algebra `S` étale over the affine line `K[X]` (with `K` infinite), the image
of `Spec S → 𝔸¹` contains a `K`-rational point. Indeed the image is open (étale is flat +
finitely presented, so `isOpenMap_comap_of_hasGoingDown_of_finitePresentation` applies) and
nonempty (`S ≠ 0`), hence contains a nonempty basic open `D(h)`; over the infinite field `K` the
nonzero polynomial `h` has a non-vanishing value `x`, and `ratPt x ∈ D(h)` lies in the image. -/
theorem exists_ratPt_mem_range [Infinite K] {S : Type u} [CommRing S]
    [Algebra (MvPolynomial (Fin 1) K) S] [Algebra.Etale (MvPolynomial (Fin 1) K) S]
    [Nontrivial S] :
    ∃ x : Fin 1 → K, ratPt x ∈ Set.range (comap (algebraMap (MvPolynomial (Fin 1) K) S)) := by
  have hopen : IsOpen (Set.range (comap (algebraMap (MvPolynomial (Fin 1) K) S))) :=
    (isOpenMap_comap_of_hasGoingDown_of_finitePresentation).isOpen_range
  obtain ⟨p, hp⟩ : (Set.range (comap (algebraMap (MvPolynomial (Fin 1) K) S))).Nonempty := by
    obtain ⟨q⟩ := (inferInstance : Nonempty (PrimeSpectrum S)); exact ⟨_, ⟨q, rfl⟩⟩
  obtain ⟨_, ⟨h, rfl⟩, hpB, hsub⟩ :=
    isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp hopen
  have hh : h ≠ 0 := by
    rintro rfl
    simp only [PrimeSpectrum.basicOpen_zero, TopologicalSpace.Opens.coe_bot,
      Set.mem_empty_iff_false] at hpB
  obtain ⟨x, hx⟩ : ∃ x : Fin 1 → K, eval x h ≠ eval x 0 :=
    not_forall.mp fun H => hh (MvPolynomial.funext_iff.mpr H)
  refine ⟨x, hsub ?_⟩
  simp only [SetLike.mem_coe]
  rw [mem_ratPt_basicOpen, MvPolynomial.aeval_eq_eval]
  simpa using hx

/-- A nonzero étale algebra over a separably closed field has a `K`-point: it splits as a finite
product of copies of `K` (`Algebra.FormallyEtale.equivPiOfIsSepClosed`), and any factor projection
is a `K`-algebra homomorphism to `K`. -/
theorem exists_algHom_to_base [IsSepClosed K] {A : Type u} [CommRing A] [Algebra K A]
    [Algebra.Etale K A] [Nontrivial A] : Nonempty (A →ₐ[K] K) := by
  have e := Algebra.FormallyEtale.equivPiOfIsSepClosed K A
  obtain ⟨p⟩ := (inferInstance : Nonempty (PrimeSpectrum A))
  exact ⟨(Pi.evalAlgHom K (fun _ : PrimeSpectrum A => K) p).comp e.toAlgHom⟩

/-- **The commutative-algebra core.** A nonzero `K`-algebra `S` which is étale over the
affine line `K[X]`, with `K` separably closed, has a `K`-point `S →ₐ[K] K`.

Proof: pick a `K`-rational point `x` of `𝔸¹` in the image of `Spec S` (`exists_ratPt_mem_range`).
The fibre `K ⊗[K[X]] S` (base change along `aeval x`) is étale over `K` (`Algebra.Etale.baseChange`)
and nonzero: a prime `q` of `S` lying over `ratPt x` gives a `K[X]`-algebra map
`K ⊗[K[X]] S → S ⧸ q` (via `AlgHom.liftOfSurjective` on the surjection `K[X] ↠ K` and the residue
map `S ↠ S ⧸ q`), whose codomain is nontrivial. Being a nonzero étale `K`-algebra over a separably
closed field, the fibre has a `K`-point (`exists_algHom_to_base`), which composes with the
`K`-algebra map `S →ₐ[K] K ⊗[K[X]] S` (`includeRight`) to a `K`-point of `S`. -/
theorem exists_algHom_of_etale_mvPoly [IsSepClosed K] {S : Type u} [CommRing S] [Algebra K S]
    [Algebra (MvPolynomial (Fin 1) K) S] [IsScalarTower K (MvPolynomial (Fin 1) K) S]
    [Algebra.Etale (MvPolynomial (Fin 1) K) S] [Nontrivial S] :
    Nonempty (S →ₐ[K] K) := by
  obtain ⟨x, hx⟩ := exists_ratPt_mem_range (K := K) (S := S)
  letI algK : Algebra (MvPolynomial (Fin 1) K) K :=
    (aeval x : MvPolynomial (Fin 1) K →ₐ[K] K).toRingHom.toAlgebra
  have hAlg : (algebraMap (MvPolynomial (Fin 1) K) K) = (aeval x).toRingHom := rfl
  haveI : IsScalarTower K (MvPolynomial (Fin 1) K) K := by
    apply IsScalarTower.of_algebraMap_eq; intro a; rw [hAlg]; simp
  haveI hetale : Algebra.Etale K (K ⊗[MvPolynomial (Fin 1) K] S) :=
    Algebra.Etale.baseChange (MvPolynomial (Fin 1) K) S K
  -- the fibre `K ⊗[K[X]] S` is nonzero
  obtain ⟨q, hq⟩ := hx
  have hsurj : Function.Surjective (Algebra.ofId (MvPolynomial (Fin 1) K) K) := by
    intro a; exact ⟨C a, by rw [Algebra.ofId_apply, hAlg]; simp⟩
  have hkerEq : RingHom.ker (algebraMap (MvPolynomial (Fin 1) K) K) =
      RingHom.ker (algebraMap (MvPolynomial (Fin 1) K) (S ⧸ q.asIdeal)) := by
    rw [IsScalarTower.algebraMap_eq (MvPolynomial (Fin 1) K) S (S ⧸ q.asIdeal),
      ← RingHom.comap_ker, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker, hAlg,
      RingHom.ker_eq_comap_bot]
    simpa [ratPt, PrimeSpectrum.comap_asIdeal] using (congrArg PrimeSpectrum.asIdeal hq).symm
  let f₁ : K →ₐ[MvPolynomial (Fin 1) K] (S ⧸ q.asIdeal) :=
    AlgHom.liftOfSurjective _ hsurj (Algebra.ofId _ _) (le_of_eq hkerEq)
  let f₂ : S →ₐ[MvPolynomial (Fin 1) K] (S ⧸ q.asIdeal) := IsScalarTower.toAlgHom _ S _
  let Φ := Algebra.TensorProduct.lift f₁ f₂ (fun _ _ => Commute.all _ _)
  haveI : q.asIdeal.IsPrime := q.2
  haveI hntq : Nontrivial (S ⧸ q.asIdeal) := inferInstance
  haveI hnt : Nontrivial (K ⊗[MvPolynomial (Fin 1) K] S) := RingHom.domain_nontrivial Φ.toRingHom
  -- split the fibre and pull the `K`-point back to `S`
  obtain ⟨φ⟩ := exists_algHom_to_base (K := K) (A := K ⊗[MvPolynomial (Fin 1) K] S)
  exact ⟨φ.comp (Algebra.TensorProduct.includeRight.restrictScalars K)⟩

/-! ## §3. The scheme-level section -/

/-- **A nonempty smooth curve over a separably closed field has a rational point.** For a scheme
`X` smooth of relative dimension `1` over a separably closed field `K`, if `X` is nonempty there is
a `K`-point `p : Spec K ⟶ X` over `K` (`p ≫ f = 𝟙`).

Note the binders: `[SmoothOfRelativeDimension 1 f]`, `[IsSepClosed K]`, `[Nonempty X]` and nothing
else — no properness, no geometric integrality. That is weaker than the curve package every
`J`-milestone carries.

Proof: a standard-smooth chart `V ∋ x₀` of relative dimension `1` gives, via
`RingHom.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial` and transport across
`Γ(Spec K, ⊤) ≅ K`, an étale `K[X]`-algebra structure on `Γ(X, V)`; the core
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
  obtain ⟨φ⟩ := exists_algHom_of_etale_mvPoly (K := K) (S := Γ(X, V))
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

/-- **Density form.** For `f : X ⟶ Spec K` smooth of relative dimension `1` over separably closed
`K` and any nonempty open `W` of `X`, there is a `K`-point of `X` over `K` whose topological image
lies in `W`. Restrict to `W` and apply the previous theorem: the class is Zariski-local at the
source, so the restriction keeps the numeral. -/
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
  · simp

end AlgebraicGeometry.SeparablyClosed

/-! ## §4. The class form, and the bridge to the base-changed curve

§3 produces `∃ p, p ≫ f = 𝟙`. What the route's consumers bind is `Scheme.HasRationalPoint`, and
what they bind it *at* is not `C` but `C_{k^s}`. Both steps are here, kept separate because they
are separate claims. -/

namespace AlgebraicGeometry.Scheme

/-- **The class form.** `Scheme.HasRationalPoint` for a curve over a separably closed field. Its
field is a `Nonempty` subtype of exactly the equation §3 produces, so this is repackaging — but it
is the form instance search can use, and no producer of this class without `[IsAlgClosed]`
existed before. -/
theorem hasRationalPoint_of_isSepClosed {K : Type u} [Field K] [IsSepClosed K]
    (C : Over (Spec (CommRingCat.of K))) [SmoothOfRelativeDimension 1 C.hom]
    [Nonempty C.left] :
    Scheme.HasRationalPoint C := by
  obtain ⟨p, hp⟩ :=
    SeparablyClosed.exists_rationalPoint_of_smoothOfRelativeDimension_one C.hom
  exact ⟨⟨p, hp⟩⟩

/-- **The bridge, and the point of the file**: for a smooth geometrically integral curve `C` over
an **arbitrary** field `k`, the base change `C_{k^s}` to a separable closure has a `k^s`-rational
point.

There is no hypothesis on `C(k)`, which is what makes this usable under `I-0491`: the section is
obtained after a separable base extension, never assumed downstairs.

**What it does and does not reach, measured rather than asserted.** It discharges the slot
`Picard/PicEtSubcanonical.lean` names when it says a section is available over a separably closed
field — `Scheme.hasRationalPoint_of_isSepClosed` closes that goal outright. It does **not** reach
campaign `G1`, which spreads `J5`'s datum to a *finite* Galois level `k'/k`: `IsSepClosed k'` does
not hold at a finite level and nothing here produces a point there. So this is the section at
`k^s`, not at the finite levels `G1` needs, and the gap between them is a separate obligation. As
of this file there are also **no formal consumers** of any declaration here; cluster `J`'s
milestones exist as campaign prose, not as Lean binders.

Three inputs, each measured:

* `IsSepClosed (SeparableClosure k)` and `Algebra k (SeparableClosure k)` are mathlib instances;
* the numeral binder survives the base change
  (`Scheme.smoothOfRelativeDimension_one_hom_baseChangeField`);
* nonemptiness of the total space comes from `GeometricallyIntegral`, stable under the field base
  change (`Scheme.geometricallyIntegral_hom_baseChangeField`), giving `IsIntegral C_{k^s}.left`
  hence `Nonempty`. The integral spelling is chosen for convenience only. An earlier revision of
  this docstring claimed the geometrically *irreducible* form "would not do" because it has no
  base-change-stability instance in this project; **that was false** — mathlib's
  `instIsStableUnderBaseChangeSchemeGeometricallyIrreducible` is in this file's own import
  closure, and `hasRationalPoint_baseChangeField_separableClosure_of_geometricallyIrreducible`
  below proves the challenge-shaped version in four lines. The mistake was reading a failed
  `inferInstance` as a mathematical absence.

Properness is **not** a binder and is not used. Decisively rather than by signature: §3 delivers a
point for an arbitrary nonempty *open* subscheme of a curve, where properness fails. -/
theorem hasRationalPoint_baseChangeField_separableClosure {k : Type u} [Field k]
    (C : Over (Spec (CommRingCat.of k))) [SmoothOfRelativeDimension 1 C.hom]
    [GeometricallyIntegral C.hom] :
    Scheme.HasRationalPoint (Scheme.baseChangeField C (SeparableClosure k)) := by
  haveI : IsIntegral (Scheme.baseChangeField C (SeparableClosure k)).left := inferInstance
  haveI : Nonempty (Scheme.baseChangeField C (SeparableClosure k)).left := IsIntegral.nonempty
  exact hasRationalPoint_of_isSepClosed (Scheme.baseChangeField C (SeparableClosure k))

/-- **The bridge at the challenge's own binder.** Same conclusion as
`hasRationalPoint_baseChangeField_separableClosure`, with `GeometricallyIrreducible` in place of
`GeometricallyIntegral` — which is what `AlgebraicJacobian/Challenge.lean` and the headline
`picardJacobianWitness` actually carry, so a consumer needs no bridging instance.

This exists because a fresh-context audit refuted the claim that the irreducible form was
unavailable: `MorphismProperty.IsStableUnderBaseChange @GeometricallyIrreducible` is a mathlib
instance already in this file's import closure, so the base change keeps the hypothesis and
`IrreducibleSpace.toNonempty` supplies nonemptiness. Recorded rather than silently replacing the
integral version, because both spellings have callers. -/
theorem hasRationalPoint_baseChangeField_separableClosure_of_geometricallyIrreducible
    {k : Type u} [Field k] (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] :
    Scheme.HasRationalPoint (Scheme.baseChangeField C (SeparableClosure k)) := by
  haveI : GeometricallyIrreducible (Scheme.baseChangeField C (SeparableClosure k)).hom :=
    MorphismProperty.pullback_snd _ _ ‹GeometricallyIrreducible C.hom›
  haveI : Nonempty (Scheme.baseChangeField C (SeparableClosure k)).left := inferInstance
  exact hasRationalPoint_of_isSepClosed (Scheme.baseChangeField C (SeparableClosure k))

/-- **The density form at the base-changed curve** — the shape `J1` and `J4` consume, rather than
the bare existence of one section.

`J1` pins an `(r−g)`-tuple of rational points of `C'` and `J4` subtracts rational points, so what
those milestones need is not a section but *points in prescribed opens*. This is
`SeparablyClosed.exists_rationalPoint_mem` at `C_{k^s}`, stated so a consumer does not have to
rebuild the base-change binders.

It does **not** by itself produce a tuple of *distinct* points: that needs the opens to be chosen
apart, which is the caller's business. What makes such a choice possible is recorded next. -/
theorem exists_rationalPoint_mem_baseChangeField_separableClosure {k : Type u} [Field k]
    (C : Over (Spec (CommRingCat.of k))) [SmoothOfRelativeDimension 1 C.hom]
    [GeometricallyIrreducible C.hom]
    (W : (Scheme.baseChangeField C (SeparableClosure k)).left.Opens)
    (hW : (W : Set (Scheme.baseChangeField C (SeparableClosure k)).left).Nonempty) :
    ∃ p : Spec (CommRingCat.of (SeparableClosure k)) ⟶
        (Scheme.baseChangeField C (SeparableClosure k)).left,
      p ≫ (Scheme.baseChangeField C (SeparableClosure k)).hom = 𝟙 _ ∧
        p.base (IsLocalRing.closedPoint (SeparableClosure k)) ∈ W :=
  SeparablyClosed.exists_rationalPoint_mem
    (Scheme.baseChangeField C (SeparableClosure k)).hom W hW

/-- **`C_{k^s}` is irreducible.** Paired with the density form above this is what lets a caller
choose points apart: on an irreducible space any two nonempty opens meet, so removing finitely
many closed points from `C_{k^s}` leaves a nonempty open to draw the next point from. Recorded
because it is the missing half of `J1`'s tuple, and it is free — geometric irreducibility is
stable under the field base change. -/
theorem irreducibleSpace_baseChangeField_separableClosure {k : Type u} [Field k]
    (C : Over (Spec (CommRingCat.of k))) [GeometricallyIrreducible C.hom] :
    IrreducibleSpace (Scheme.baseChangeField C (SeparableClosure k)).left := by
  haveI : GeometricallyIrreducible (Scheme.baseChangeField C (SeparableClosure k)).hom :=
    MorphismProperty.pullback_snd _ _ ‹GeometricallyIrreducible C.hom›
  exact irreducibleSpace_left_of_geometricallyIrreducible
    (Scheme.baseChangeField C (SeparableClosure k))

end AlgebraicGeometry.Scheme

