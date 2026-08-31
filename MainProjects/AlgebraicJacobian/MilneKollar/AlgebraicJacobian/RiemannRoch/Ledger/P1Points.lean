/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Ledger.P1Charts
import AlgebraicJacobian.RiemannRoch.Ledger.StalksDVR

/-!
# Points of the projective line, and morphisms to it from chart data

Two groups of results about `P1 k` feeding the construction of the finite map `C ⟶ ℙ¹`.

**Morphisms into `ℙ¹` from an element of a ring.**  For a ring `A` under `k` (a morphism
`ρ : k ⟶ A` of rings) and an element `a : A`, `P1.fromSpecChart k ρ i a : Spec A ⟶ P1 k` is
the morphism through the chart `D₊(Xᵢ)` sending the chart coordinate to `a`:

* `P1.fromSpecChart_structureMap`: it is a morphism over `k`;
* `P1.SpecMap_fromSpecChart`: it is natural in `A`;
* `P1.fromSpecChart_isUnit`: **the gluing identity** — for a unit `u`, the morphism
  `[1 : u]` through chart `0` equals the morphism `[u⁻¹ : 1]` through chart `1`.  This is
  the entire content of "the loci `U_f` and `U_{1/f}` glue to a morphism to `ℙ¹`",
  concentrated in a single point-free identity: both morphisms factor through the chart
  overlap `D₊(X₀X₁)`, where they are induced by the same ring homomorphism (the
  localization lift sending the overlap coordinate `T = X₁/X₀` to `u`).
* `P1.fromSpecChart_base_genericPoint`: if the evaluation `k[t] → A`, `t ↦ a` is injective
  ("`a` is transcendental"), the generic point of `Spec A` lands on the generic point of
  `ℙ¹`.

**The topology of `ℙ¹`.**  `P1 k` is an irreducible, separated scheme; its charts have
Dedekind section rings, so its specialization order has height one
(`P1.specializes_eq_genericPoint_or_eq`); and it has a point besides the generic one
(`P1.exists_ne_genericPoint`).  Consequently every non-generic point of `ℙ¹` is closed
(`P1.isClosed_singleton_of_ne_genericPoint`).
-/

set_option autoImplicit false

universe u

open CategoryTheory MvPolynomial HomogeneousLocalization

namespace AlgebraicGeometry

namespace P1

variable (k : Type u) [Field k]

/-- The standard grading of `k[X₀, X₁]`, the graded ring underlying `P1 k`. -/
local notation "𝒜" => homogeneousSubmodule (Fin 2) k

/-! ### Domain and Dedekind instances for the chart rings -/

instance : IsDomain (Away 𝒜 (X (0 : Fin 2))) :=
  MulEquiv.isDomain (Polynomial k) (awayAlgEquiv k fin_zero_ne_one).toRingEquiv.toMulEquiv

instance : IsDomain (Away 𝒜 (X (1 : Fin 2))) :=
  MulEquiv.isDomain (Polynomial k) (awayAlgEquiv k fin_one_ne_zero).toRingEquiv.toMulEquiv

instance : Nontrivial (Away 𝒜 ((X 0 : MvPolynomial (Fin 2) k) * X 1)) :=
  (overlapAlgEquiv k).toEquiv.nontrivial

/-- The section ring of a standard chart of `ℙ¹` is a principal ideal ring: it is `k[t]`. -/
theorem isPrincipalIdealRing_chartSections (i : Fin 2) :
    IsPrincipalIdealRing Γ(P1 k, chartOpen k i) := by
  fin_cases i
  · exact IsPrincipalIdealRing.of_surjective (chartSectionsEquiv₀ k).symm.toRingHom
      (chartSectionsEquiv₀ k).symm.surjective
  · exact IsPrincipalIdealRing.of_surjective (chartSectionsEquiv₁ k).symm.toRingHom
      (chartSectionsEquiv₁ k).symm.surjective

/-- The section ring of a standard chart of `ℙ¹` is a domain: it is `k[t]`. -/
theorem isDomain_chartSections (i : Fin 2) : IsDomain Γ(P1 k, chartOpen k i) := by
  fin_cases i
  · exact MulEquiv.isDomain (Polynomial k) (chartSectionsEquiv₀ k).toMulEquiv
  · exact MulEquiv.isDomain (Polynomial k) (chartSectionsEquiv₁ k).toMulEquiv

/-- The section ring of a standard chart of `ℙ¹` is a Dedekind domain: it is `k[t]`. -/
theorem isDedekindDomain_chartSections (i : Fin 2) :
    IsDedekindDomain Γ(P1 k, chartOpen k i) :=
  letI := isDomain_chartSections k i
  letI := isPrincipalIdealRing_chartSections k i
  inferInstance

/-! ### The topology of `ℙ¹`: irreducibility, height one, closed points -/

/-- Every nonempty open subset of `ℙ¹` meets the chart `D₊(X₀)`: a point outside `D₊(X₀)`
lies in the chart `D₊(X₁) ≅ Spec k[t]`, whose every nonempty open meets the (nonempty)
preimage of the chart overlap. -/
theorem exists_mem_chartOpen_zero_of_isOpen {W : Set (P1 k)} (hW : IsOpen W)
    (hne : W.Nonempty) : ∃ z ∈ W, z ∈ chartOpen k 0 := by
  obtain ⟨w, hw⟩ := hne
  have hcover : w ∈ chartOpen k 0 ⊔ chartOpen k 1 := by
    rw [chartOpen_sup]; trivial
  rw [TopologicalSpace.Opens.mem_sup] at hcover
  rcases hcover with h0 | h1
  · exact ⟨w, hw, h0⟩
  rw [← opensRange_chartι k 1] at h1
  obtain ⟨y, hy⟩ := h1
  -- The preimage of `W` in the chart is a nonempty open; so is the preimage of the
  -- overlap; the chart is irreducible, so they intersect.
  have hOne : ((chartι k 1).base ⁻¹' (chartOpen k 0 : Set (P1 k))).Nonempty := by
    obtain ⟨z⟩ : Nonempty (Spec (CommRingCat.of
        (Away 𝒜 ((X 0 : MvPolynomial (Fin 2) k) * X 1)))) := inferInstance
    have hpover : (Proj.awayι 𝒜 _ (X_mul_X_mem k) two_pos).base z ∈
        Proj.basicOpen 𝒜 ((X 0 : MvPolynomial (Fin 2) k) * X 1) := by
      rw [← Proj.opensRange_awayι 𝒜 _ (X_mul_X_mem k) two_pos]
      exact ⟨z, rfl⟩
    have hp1 : (Proj.awayι 𝒜 _ (X_mul_X_mem k) two_pos).base z ∈ chartOpen k 1 :=
      overlap_le_right k hpover
    rw [← opensRange_chartι k 1] at hp1
    obtain ⟨y', hy'⟩ := hp1
    exact ⟨y', by rw [Set.mem_preimage, hy']; exact overlap_le_left k hpover⟩
  have hdense : Dense ((chartι k 1).base ⁻¹' (chartOpen k 0 : Set (P1 k))) :=
    IsOpen.dense ((chartOpen k 0).2.preimage (chartι k 1).continuous) hOne
  obtain ⟨y₀, hy₀W, hy₀O⟩ := hdense.inter_open_nonempty _
    (hW.preimage (chartι k 1).continuous) ⟨y, by rwa [Set.mem_preimage, hy]⟩
  exact ⟨(chartι k 1).base y₀, hy₀W, hy₀O⟩

instance : IrreducibleSpace (P1 k) := by
  have hne : Nonempty (P1 k) :=
    ⟨(chartι k 0).base (Nonempty.some inferInstance)⟩
  refine { toPreirreducibleSpace := ⟨?_⟩, toNonempty := hne }
  rintro u v hu hv ⟨a, -, ha⟩ ⟨b, -, hb⟩
  obtain ⟨a', ha'u, ha'0⟩ := exists_mem_chartOpen_zero_of_isOpen k hu ⟨a, ha⟩
  obtain ⟨b', hb'v, hb'0⟩ := exists_mem_chartOpen_zero_of_isOpen k hv ⟨b, hb⟩
  rw [← opensRange_chartι k 0] at ha'0 hb'0
  obtain ⟨a'', ha''⟩ := ha'0
  obtain ⟨b'', hb''⟩ := hb'0
  -- Intersect the preimages inside the irreducible chart `Spec (k[X₀,X₁]_(X₀))₀`.
  have hdense : Dense ((chartι k 0).base ⁻¹' u) :=
    IsOpen.dense (hu.preimage (chartι k 0).continuous)
      ⟨a'', by rwa [Set.mem_preimage, ha'']⟩
  obtain ⟨y₀, hy₀v, hy₀u⟩ := hdense.inter_open_nonempty _
    (hv.preimage (chartι k 0).continuous) ⟨b'', by rwa [Set.mem_preimage, hb'']⟩
  exact ⟨(chartι k 0).base y₀, trivial, hy₀u, hy₀v⟩

/-- The generic point of the chart `D₊(X₀)` is the generic point of `ℙ¹`. -/
theorem chartι_base_genericPoint :
    (chartι k 0).base (genericPoint (Spec (CommRingCat.of (Away 𝒜 (X (0 : Fin 2)))))) =
      genericPoint (P1 k) :=
  genericPoint_eq_of_isOpenImmersion (chartι k 0)

/-- `ℙ¹` has a point besides the generic point (the origin of the chart `D₊(X₀)`). -/
theorem exists_ne_genericPoint : ∃ z : P1 k, z ≠ genericPoint (P1 k) := by
  have hnf : ¬IsField (Away 𝒜 (X (0 : Fin 2))) := fun h =>
    Polynomial.not_isField k
      ((awayAlgEquiv k fin_zero_ne_one).symm.toRingEquiv.toMulEquiv.isField h)
  obtain ⟨p, hp0, hp⟩ := Ring.not_isField_iff_exists_prime.mp hnf
  refine ⟨(chartι k 0).base ⟨p, hp⟩, fun h => hp0 ?_⟩
  rw [← chartι_base_genericPoint, genericPoint_eq_bot_of_affine] at h
  have := (chartι k 0).isOpenEmbedding.injective h
  exact congrArg PrimeSpectrum.asIdeal this

/-- On `ℙ¹`, the only generalizations of a point are the generic point and the point
itself. -/
theorem specializes_eq_genericPoint_or_eq {x y : P1 k} (h : y ⤳ x) :
    y = genericPoint (P1 k) ∨ y = x := by
  have hx : x ∈ chartOpen k 0 ⊔ chartOpen k 1 := by
    rw [chartOpen_sup]; trivial
  rw [TopologicalSpace.Opens.mem_sup] at hx
  rcases hx with h0 | h1
  · exact (isAffineOpen_chartOpen k 0).specializes_eq_genericPoint_or_eq
      (isDedekindDomain_chartSections k 0) h0 h
  · exact (isAffineOpen_chartOpen k 1).specializes_eq_genericPoint_or_eq
      (isDedekindDomain_chartSections k 1) h1 h

/-- Every non-generic point of `ℙ¹` is closed. -/
theorem isClosed_singleton_of_ne_genericPoint {x : P1 k} (hx : x ≠ genericPoint (P1 k)) :
    IsClosed ({x} : Set (P1 k)) :=
  Scheme.isClosed_singleton_of_forall_specializes
    (fun _ _ h => specializes_eq_genericPoint_or_eq k h) hx

instance : (P1 k).IsSeparated :=
  ⟨by rw [← Limits.terminal.comp_from (structureMap k)]; infer_instance⟩

/-! ### Morphisms to `ℙ¹` through a chart -/

section FromSpecChart

variable {A : CommRingCat.{u}} (ρ : CommRingCat.of k ⟶ A)

/-- The evaluation of the section ring of the chart `D₊(Xᵢ)` in a ring `A` under `k`,
sending the chart coordinate to `a`. -/
noncomputable def chartEval (i : Fin 2) (a : A) : CommRingCat.of (Away 𝒜 (X i)) ⟶ A :=
  CommRingCat.ofHom ((Polynomial.eval₂RingHom ρ.hom a).comp (awayToPoly k i).toRingHom)

theorem chartEval_apply (i : Fin 2) (a : A) (z : Away 𝒜 (X i)) :
    (chartEval k ρ i a).hom z = Polynomial.eval₂ ρ.hom a (awayToPoly k i z) := rfl

theorem chartEval_chartCoord {i j : Fin 2} (hij : i ≠ j) (a : A) :
    (chartEval k ρ i a).hom (chartCoord k i j) = a := by
  rw [chartEval_apply, awayToPoly_chartCoord k hij, Polynomial.eval₂_X]

theorem chartEval_algebraMap (i : Fin 2) (a : A) (r : k) :
    (chartEval k ρ i a).hom (algebraMap k (Away 𝒜 (X i)) r) = ρ.hom r := by
  rw [chartEval_apply, AlgHom.commutes, Polynomial.algebraMap_eq, Polynomial.eval₂_C]

/-- The morphism `Spec A ⟶ ℙ¹` through the chart `D₊(Xᵢ)` sending the chart coordinate to
`a : A`; for `i = 0` this is the "point" `[1 : a]`, for `i = 1` it is `[a : 1]`. -/
noncomputable def fromSpecChart (i : Fin 2) (a : A) : Spec A ⟶ P1 k :=
  Spec.map (chartEval k ρ i a) ≫ chartι k i

/-- `fromSpecChart` is a morphism over `k`. -/
theorem fromSpecChart_structureMap (i : Fin 2) (a : A) :
    fromSpecChart k ρ i a ≫ structureMap k = Spec.map ρ := by
  rw [fromSpecChart, Category.assoc, chartι_structureMap, ← Spec.map_comp]
  congr 1
  ext r
  exact chartEval_algebraMap k ρ i a r

/-- `fromSpecChart` is natural in the ring `A`. -/
theorem SpecMap_fromSpecChart {A' : CommRingCat.{u}} (g : A ⟶ A') (i : Fin 2) (a : A) :
    Spec.map g ≫ fromSpecChart k ρ i a = fromSpecChart k (ρ ≫ g) i (g.hom a) := by
  rw [fromSpecChart, fromSpecChart, ← Category.assoc, ← Spec.map_comp]
  congr 2
  ext z
  change g.hom (Polynomial.eval₂ ρ.hom a (awayToPoly k i z)) =
    Polynomial.eval₂ (ρ ≫ g).hom (g.hom a) (awayToPoly k i z)
  rw [Polynomial.hom_eval₂, CommRingCat.hom_comp]

/-! ### The gluing identity -/

/-- The restriction of the chart `D₊(X₀)` to the overlap, as a factorization of the chart
inclusion of `D₊(X₀X₁)`. -/
theorem SpecMap_awayToOverlapLeft_chartι :
    Spec.map (CommRingCat.ofHom (awayToOverlapLeft k)) ≫ chartι k 0 =
      Proj.awayι 𝒜 ((X 0 : MvPolynomial (Fin 2) k) * X 1) (X_mul_X_mem k) two_pos := by
  rw [awayToOverlapLeft_eq]
  exact Proj.SpecMap_awayMap_awayι 𝒜 (X_mem k 0) one_pos (X_mem k 1) rfl

/-- The restriction of the chart `D₊(X₁)` to the overlap, as a factorization of the chart
inclusion of `D₊(X₀X₁)`. -/
theorem SpecMap_awayToOverlapRight_chartι :
    Spec.map (CommRingCat.ofHom (awayToOverlapRight k)) ≫ chartι k 1 =
      Proj.awayι 𝒜 ((X 0 : MvPolynomial (Fin 2) k) * X 1) (X_mul_X_mem k) two_pos := by
  rw [awayToOverlapRight_eq]
  exact Proj.SpecMap_awayMap_awayι 𝒜 (X_mem k 1) one_pos (X_mem k 0) (mul_comm (X 0) (X 1))

/-- The algebra structure of the overlap ring over the left chart ring is restriction. -/
theorem algebraMap_awayToOverlapLeft :
    algebraMap (Away 𝒜 (X (0 : Fin 2)))
        (Away 𝒜 ((X 0 : MvPolynomial (Fin 2) k) * X 1)) = awayToOverlapLeft k :=
  rfl

/-- **The gluing identity**: for a unit `u` of `A`, the morphism `[1 : u]` through chart `0`
agrees with the morphism `[u⁻¹ : 1]` through chart `1`.  Both factor through the chart
overlap `D₊(X₀X₁)`, where they are induced by the same ring homomorphism, namely the
localization lift sending the overlap coordinate `T = X₁/X₀` to `u`. -/
theorem fromSpecChart_units (u : Aˣ) :
    fromSpecChart k ρ 0 (u : A) = fromSpecChart k ρ 1 ((u⁻¹ : Aˣ) : A) := by
  have hunit : IsUnit ((chartEval k ρ 0 (u : A)).hom (chartCoord k 0 1)) := by
    rw [chartEval_chartCoord k ρ fin_zero_ne_one]
    exact u.isUnit
  set ψ : Away 𝒜 ((X 0 : MvPolynomial (Fin 2) k) * X 1) →+* A :=
    IsLocalization.Away.lift (chartCoord k 0 1) hunit with hψ
  -- `ψ` restricted to the left chart is the evaluation at `u`.
  have hleft : ψ.comp (awayToOverlapLeft k) = (chartEval k ρ 0 (u : A)).hom := by
    refine RingHom.ext fun z => ?_
    rw [RingHom.comp_apply, ← algebraMap_awayToOverlapLeft]
    exact IsLocalization.Away.lift_eq (chartCoord k 0 1) hunit z
  have hTu : ψ (awayToOverlapLeft k (chartCoord k 0 1)) = (u : A) :=
    (RingHom.congr_fun hleft (chartCoord k 0 1)).trans
      (chartEval_chartCoord k ρ fin_zero_ne_one (u : A))
  -- `ψ` sends the coordinate of the right chart to `u⁻¹`.
  have hSu : ψ (awayToOverlapRight k (chartCoord k 1 0)) = ((u⁻¹ : Aˣ) : A) := by
    have hmul := congrArg ψ (awayToOverlap_mul_eq_one k)
    rw [map_mul, map_one, hTu] at hmul
    exact (Units.inv_eq_of_mul_eq_one_right hmul).symm
  -- `ψ` restricted to the right chart is the evaluation at `u⁻¹`.
  have hbase : (ψ.comp (awayToOverlapRight k)).comp (algebraMap k (Away 𝒜 (X 1))) = ρ.hom := by
    refine RingHom.ext fun c => ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, awayToOverlapRight_algebraMap,
      ← awayToOverlapLeft_algebraMap, ← RingHom.comp_apply, hleft]
    exact chartEval_algebraMap k ρ 0 (u : A) c
  have hright : ψ.comp (awayToOverlapRight k) = (chartEval k ρ 1 ((u⁻¹ : Aˣ) : A)).hom := by
    refine RingHom.ext fun z => ?_
    obtain ⟨p, rfl⟩ := polyToAway_surjective k fin_one_ne_zero z
    rw [chartEval_apply, awayToPoly_polyToAway_apply k fin_one_ne_zero]
    change (ψ.comp (awayToOverlapRight k)) (Polynomial.aeval (chartCoord k 1 0) p) = _
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂, hbase, RingHom.comp_apply, hSu]
  -- Both morphisms factor through the overlap chart via `ψ`.
  have hfactor₀ : chartEval k ρ 0 (u : A) =
      CommRingCat.ofHom (awayToOverlapLeft k) ≫ CommRingCat.ofHom ψ := by
    ext z
    exact (RingHom.congr_fun hleft z).symm
  have hfactor₁ : chartEval k ρ 1 ((u⁻¹ : Aˣ) : A) =
      CommRingCat.ofHom (awayToOverlapRight k) ≫ CommRingCat.ofHom ψ := by
    ext z
    exact (RingHom.congr_fun hright z).symm
  rw [fromSpecChart, fromSpecChart, hfactor₀, hfactor₁, Spec.map_comp, Spec.map_comp,
    Category.assoc, Category.assoc, SpecMap_awayToOverlapLeft_chartι,
    SpecMap_awayToOverlapRight_chartι]

/-! ### The image of a transcendental point -/

/-- If the evaluation `k[t] → A`, `t ↦ a` kills no nonzero polynomial, then the generic
point of `Spec A` (for `A` a domain) is sent by `fromSpecChart k ρ 0 a` to the generic point
of `ℙ¹`. -/
theorem fromSpecChart_base_genericPoint [IsDomain A] (a : A)
    (hinj : ∀ P : Polynomial k, P ≠ 0 → Polynomial.eval₂ ρ.hom a P ≠ 0) :
    (fromSpecChart k ρ 0 a).base (genericPoint (Spec A)) = genericPoint (P1 k) := by
  have hker : Function.Injective (chartEval k ρ 0 a).hom := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨p, rfl⟩ := polyToAway_surjective k fin_zero_ne_one z
    rw [chartEval_apply, awayToPoly_polyToAway_apply k fin_zero_ne_one] at hz
    by_contra hzne
    exact hinj p (fun h0 => hzne (by rw [h0, map_zero])) hz
  have h1 : (Spec.map (chartEval k ρ 0 a)).base (genericPoint (Spec A)) =
      genericPoint (Spec (CommRingCat.of (Away 𝒜 (X (0 : Fin 2))))) := by
    rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
    refine PrimeSpectrum.ext ?_
    exact Ideal.comap_bot_of_injective _ hker
  rw [fromSpecChart, Scheme.Hom.comp_apply, h1, chartι_base_genericPoint]

end FromSpecChart

end P1

end AlgebraicGeometry
