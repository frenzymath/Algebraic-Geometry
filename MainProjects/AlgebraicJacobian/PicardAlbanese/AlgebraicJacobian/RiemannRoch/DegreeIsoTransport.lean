/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Algebra.LocalizedColength
import AlgebraicJacobian.RiemannRoch.DegreeBaseFieldInvariance

/-!
# Transport legs for degree invariance along isomorphisms (W7-B3 substrate)

The reusable plumbing under `RiemannRoch/ClassDegMapIso.lean` (W7-B3, the
`classDeg_map_iso` keystone of `informal/deg-d5b-worksheet.md` §3 /
`informal/w7-worksheet.md` §D2 B-3):

* the pure-algebra transport of the maximal-adic multiplicity along a ring isomorphism of
  local Dedekind domains (via the landed `mem_pow_iff_le_count` dictionary of
  `Algebra/LocalizedColength.lean` — no colength);
* `ord` transport along a scheme isomorphism (`ord_functionFieldMap_germ_of_isIso`), read
  through the stalk isomorphism at the unique preimage point;
* `AlgebraicGeometry.overAlgebraMap_app` — naturality of the structure map on sections
  along a morphism of schemes over `Spec K`;
* `AlgebraicGeometry.residueDeg_eq_of_isIso` — residue degrees are preserved by a
  `K`-isomorphism (the residue-field transport leg);
* `AlgebraicGeometry.pointPullbackEquations` with
  `pointPullbackEquations_presentation_elem_of_eq`/`_of_ne` — the pullback of the tracked
  point equations along **any** morphism mapping generic point to generic point (the
  generic form of the E-iv-alg step-4 plumbing of
  `RiemannRoch/DegreeBaseFieldInvariance.lean`, reusable by the E-v campaign);
* `AlgebraicGeometry.ordZ_pointPullbackUnit` — along an isomorphism, the pulled
  uniformizer has order `+1` at the unique preimage point (the degenerate fiber
  coefficient).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits UniqueFactorizationMonoid IsDedekindDomain

namespace AlgebraicGeometry

/-! ## Transport of the adic multiplicity along an isomorphism of local Dedekind domains

The stalk of a curve at a closed point is a local Dedekind domain (a DVR); an isomorphism
of schemes induces a ring isomorphism of stalks, and the multiplicity of the maximal ideal
in the factorization of a principal ideal is preserved.  This is the entire quantitative
content of the degenerate fiber-degree identity: no colength, no `Σ e·f`. -/

section RingEquivTransport

variable {A B : Type u} [CommRing A] [IsDedekindDomain A] [IsLocalRing A]
  [CommRing B] [IsDedekindDomain B] [IsLocalRing B]

omit [IsDedekindDomain A] [IsDedekindDomain B] in
/-- A ring isomorphism of local rings maps the maximal ideal onto the maximal ideal. -/
private lemma map_ringEquiv_maximalIdeal (e : A ≃+* B) :
    Ideal.map (e : A →+* B) (IsLocalRing.maximalIdeal A) = IsLocalRing.maximalIdeal B := by
  refine le_antisymm (Ideal.map_le_iff_le_comap.mpr fun a ha => Ideal.mem_comap.mpr ?_)
    fun b hb => ?_
  · by_contra hmem
    have hu : IsUnit a := by
      simpa using (IsLocalRing.notMem_maximalIdeal.mp hmem).map e.symm.toRingHom
    exact IsLocalRing.notMem_maximalIdeal.mpr hu ha
  · have hb' : e.symm b ∈ IsLocalRing.maximalIdeal A := by
      by_contra hmem
      have hu : IsUnit b := by
        simpa using (IsLocalRing.notMem_maximalIdeal.mp hmem).map e.toRingHom
      exact IsLocalRing.notMem_maximalIdeal.mpr hu hb
    simpa using Ideal.mem_map_of_mem (e : A →+* B) hb'

omit [IsDedekindDomain A] [IsDedekindDomain B] in
/-- Membership in powers of the maximal ideal transports along a ring isomorphism of
local rings. -/
private lemma mem_maximalIdeal_pow_ringEquiv_iff (e : A ≃+* B) (c : A) (n : ℕ) :
    e c ∈ IsLocalRing.maximalIdeal B ^ n ↔ c ∈ IsLocalRing.maximalIdeal A ^ n := by
  rw [← map_ringEquiv_maximalIdeal e, ← Ideal.map_pow]
  constructor
  · intro h
    obtain ⟨a, ha, hae⟩ := (Ideal.mem_map_iff_of_surjective _ e.surjective).mp h
    rwa [← e.injective hae]
  · exact fun h => Ideal.mem_map_of_mem _ h

/-- **Multiplicity transport**: a ring isomorphism of local Dedekind domains preserves the
multiplicity of the maximal ideal in the factorization of the principal ideal `(c)`. -/
private lemma count_factors_span_ringEquiv
    (vA : HeightOneSpectrum A) (hvA : vA.asIdeal = IsLocalRing.maximalIdeal A)
    (vB : HeightOneSpectrum B) (hvB : vB.asIdeal = IsLocalRing.maximalIdeal B)
    (e : A ≃+* B) {c : A} (hc : c ≠ 0) :
    Multiset.count vB.asIdeal (factors (Ideal.span {e c}))
      = Multiset.count vA.asIdeal (factors (Ideal.span {c})) := by
  have hec : e c ≠ 0 := fun h => hc (by simpa using congrArg e.symm h)
  refine le_antisymm ?_ ?_
  · refine (mem_pow_iff_le_count vA hc _).mp ?_
    rw [hvA]
    refine (mem_maximalIdeal_pow_ringEquiv_iff e c _).mp ?_
    rw [← hvB]
    exact (mem_pow_iff_le_count vB hec _).mpr le_rfl
  · refine (mem_pow_iff_le_count vB hec _).mp ?_
    rw [hvB]
    refine (mem_maximalIdeal_pow_ringEquiv_iff e c _).mpr ?_
    rw [← hvA]
    exact (mem_pow_iff_le_count vA hc _).mpr le_rfl

/-- **`intValuation` transport**: a ring isomorphism of local Dedekind domains intertwines
the adic valuations of the maximal ideals. -/
private lemma intValuation_ringEquiv
    (vA : HeightOneSpectrum A) (hvA : vA.asIdeal = IsLocalRing.maximalIdeal A)
    (vB : HeightOneSpectrum B) (hvB : vB.asIdeal = IsLocalRing.maximalIdeal B)
    (e : A ≃+* B) {c : A} (hc : c ≠ 0) :
    vB.intValuation (e c) = vA.intValuation c := by
  have hec : e c ≠ 0 := fun h => hc (by simpa using congrArg e.symm h)
  rw [intValuation_eq_exp_neg_count vB hec, intValuation_eq_exp_neg_count vA hc,
    count_factors_span_ringEquiv vA hvA vB hvB e hc]

end RingEquivTransport

/-! ## Transport of `ord` along a scheme isomorphism -/

section OrdTransport

variable (K : Type u) [Field K] {W X : Scheme.{u}}
  [W.Over (Spec (CommRingCat.of K))] [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (W ↘ Spec (CommRingCat.of K))] [IsIntegral W]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]

/-- **`ord` transport along an isomorphism, germ form**: for an isomorphism `f : W ⟶ X`
of curve bundles, a closed point `z` of `W`, and a section `s` near `f(z)` with nonzero
germ, the order of the pulled-back rational function `f^♯(germ_η s)` at `z` equals the
order of `germ_η s` at `f(z)`.  Both orders are the adic valuations of the DVR stalks,
compared through the stalk isomorphism `f.stalkMap z`. -/
private lemma ord_functionFieldMap_germ_of_isIso (f : W ⟶ X) [IsIso f]
    (hgen : f.base (genericPoint W) = genericPoint X)
    {z : W} (hz : z ≠ genericPoint W) (hfz : f.base z ≠ genericPoint X)
    {U : X.Opens} (hηU : genericPoint X ∈ U) (hfzU : f.base z ∈ U) (s : Γ(X, U))
    (hs : (X.presheaf.germ U (f.base z) hfzU).hom s ≠ 0) :
    Scheme.ord (W ↘ Spec (CommRingCat.of K)) hz
        ((f.functionFieldMap hgen).hom ((X.presheaf.germ U (genericPoint X) hηU).hom s))
      = Scheme.ord (X ↘ Spec (CommRingCat.of K)) hfz
          ((X.presheaf.germ U (genericPoint X) hηU).hom s) := by
  letI := isDiscreteValuationRing_stalk (W ↘ Spec (CommRingCat.of K)) hz
  letI := isDedekindDomain_stalk (W ↘ Spec (CommRingCat.of K)) hz
  letI := isDiscreteValuationRing_stalk (X ↘ Spec (CommRingCat.of K)) hfz
  letI := isDedekindDomain_stalk (X ↘ Spec (CommRingCat.of K)) hfz
  have hzU' : z ∈ f ⁻¹ᵁ U := hfzU
  have hηU' : genericPoint W ∈ f ⁻¹ᵁ U := by
    change f.base (genericPoint W) ∈ U
    rw [hgen]
    exact hηU
  set c : X.presheaf.stalk (f.base z) := (X.presheaf.germ U (f.base z) hfzU).hom s with hcdef
  have hΦ : (f.functionFieldMap hgen).hom ((X.presheaf.germ U (genericPoint X) hηU).hom s)
      = (W.presheaf.germ (f ⁻¹ᵁ U) (genericPoint W) hηU').hom ((f.app U).hom s) :=
    f.functionFieldMap_germ hgen U hηU hηU' s
  have hW : (W.presheaf.germ (f ⁻¹ᵁ U) (genericPoint W) hηU').hom ((f.app U).hom s)
      = algebraMap (W.presheaf.stalk z) W.functionField
          ((W.presheaf.germ (f ⁻¹ᵁ U) z hzU').hom ((f.app U).hom s)) :=
    Scheme.germ_generic_eq_algebraMap_germ hηU' hzU' _
  have hψ : (W.presheaf.germ (f ⁻¹ᵁ U) z hzU').hom ((f.app U).hom s)
      = (f.stalkMap z).hom c :=
    (f.germ_stalkMap_apply U z hfzU s).symm
  have hX : (X.presheaf.germ U (genericPoint X) hηU).hom s
      = algebraMap (X.presheaf.stalk (f.base z)) X.functionField c :=
    Scheme.germ_generic_eq_algebraMap_germ hηU hfzU s
  have hordW : Scheme.ord (W ↘ Spec (CommRingCat.of K)) hz
      = (stalkHeightOne W z).valuation W.functionField := rfl
  have hordX : Scheme.ord (X ↘ Spec (CommRingCat.of K)) hfz
      = (stalkHeightOne X (f.base z)).valuation X.functionField := rfl
  calc Scheme.ord (W ↘ Spec (CommRingCat.of K)) hz
        ((f.functionFieldMap hgen).hom ((X.presheaf.germ U (genericPoint X) hηU).hom s))
      = (stalkHeightOne W z).valuation W.functionField
          (algebraMap (W.presheaf.stalk z) W.functionField ((f.stalkMap z).hom c)) := by
        rw [hordW, hΦ, hW, hψ]
    _ = (stalkHeightOne W z).intValuation ((f.stalkMap z).hom c) :=
        (stalkHeightOne W z).valuation_of_algebraMap ((f.stalkMap z).hom c)
    _ = (stalkHeightOne X (f.base z)).intValuation c :=
        intValuation_ringEquiv _ rfl _ rfl
          ((asIso (f.stalkMap z)).commRingCatIsoToRingEquiv) hs
    _ = Scheme.ord (X ↘ Spec (CommRingCat.of K)) hfz
          ((X.presheaf.germ U (genericPoint X) hηU).hom s) := by
        rw [hordX, hX, (stalkHeightOne X (f.base z)).valuation_of_algebraMap c]

end OrdTransport

/-! ## Transport of the residue degree along a `K`-isomorphism -/

section ResidueTransport

attribute [local instance] Scheme.residueFieldOverModule

variable (K : Type u) [Field K] {W X : Scheme.{u}}
  [W.Over (Spec (CommRingCat.of K))] [X.Over (Spec (CommRingCat.of K))]

/-- **Naturality of the structure map on sections**: for a morphism `f : W ⟶ X` of schemes
over `Spec K` (witnessed by `hover`), applying `f` to the canonical image of `a : K` in
`Γ(X, U)` gives the canonical image of `a` in `Γ(W, f ⁻¹ᵁ U)`. -/
lemma overAlgebraMap_app (f : W ⟶ X)
    (hover : f ≫ (X ↘ Spec (CommRingCat.of K)) = W ↘ Spec (CommRingCat.of K))
    (U : X.Opens) (a : K) :
    (f.app U).hom (X.overAlgebraMap K U a) = W.overAlgebraMap K (f ⁻¹ᵁ U) a := by
  have hnat : X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ f.app U
      = f.appTop ≫ W.presheaf.map (homOfLE (le_top : f ⁻¹ᵁ U ≤ ⊤)).op :=
    f.naturality (homOfLE (le_top : U ≤ ⊤)).op
  have harrow : ((Scheme.ΓSpecIso (CommRingCat.of K)).inv
        ≫ (X ↘ Spec (CommRingCat.of K)).appTop
        ≫ X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op) ≫ f.app U
      = (Scheme.ΓSpecIso (CommRingCat.of K)).inv
        ≫ (W ↘ Spec (CommRingCat.of K)).appTop
        ≫ W.presheaf.map (homOfLE (le_top : f ⁻¹ᵁ U ≤ ⊤)).op := by
    rw [Category.assoc, Category.assoc, hnat, ← hover, Scheme.Hom.comp_appTop]
    simp only [Category.assoc]
  have h1 : (f.app U).hom (X.overAlgebraMap K U a)
      = (((Scheme.ΓSpecIso (CommRingCat.of K)).inv
          ≫ (X ↘ Spec (CommRingCat.of K)).appTop
          ≫ X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op) ≫ f.app U).hom a := by
    rw [CommRingCat.comp_apply]
    rfl
  rw [h1, harrow]
  rfl

/-- **The residue degree is preserved by a `K`-isomorphism**: for an isomorphism
`f : W ⟶ X` of schemes over `Spec K` and any point `z : W`,
`[κ(z) : K] = [κ(f z) : K]`.  The stalk isomorphism `f.stalkMap z` induces a ring
isomorphism of residue fields which is `K`-linear by `overAlgebraMap_app`, and `K`-linear
equivalences preserve `finrank`. -/
theorem residueDeg_eq_of_isIso (f : W ⟶ X) [IsIso f]
    (hover : f ≫ (X ↘ Spec (CommRingCat.of K)) = W ↘ Spec (CommRingCat.of K)) (z : W) :
    W.residueDeg K z = X.residueDeg K (f.base z) := by
  have hstalk : ∀ a : K, (f.stalkMap z).hom
      ((X.presheaf.germ ⊤ (f.base z) trivial).hom (X.overAlgebraMap K ⊤ a))
      = (W.presheaf.germ ⊤ z trivial).hom (W.overAlgebraMap K ⊤ a) := by
    intro a
    rw [f.germ_stalkMap_apply ⊤ z trivial (X.overAlgebraMap K ⊤ a),
      overAlgebraMap_app K f hover ⊤ a]
    have hres : W.overAlgebraMap K (f ⁻¹ᵁ ⊤) a
        = (W.presheaf.map (homOfLE (le_top : f ⁻¹ᵁ ⊤ ≤ ⊤)).op).hom
            (W.overAlgebraMap K ⊤ a) :=
      (W.overAlgebraMap_apply_res K (homOfLE (le_top : f ⁻¹ᵁ ⊤ ≤ ⊤)).op a).symm
    rw [hres, W.presheaf.germ_res_apply (homOfLE (le_top : f ⁻¹ᵁ ⊤ ≤ ⊤)) z trivial]
  let r : X.residueField (f.base z) ≃+* W.residueField z :=
    IsLocalRing.ResidueField.mapEquiv (asIso (f.stalkMap z)).commRingCatIsoToRingEquiv
  -- `K`-compatibility of the residue-field isomorphism
  have hcompat : ∀ a : K,
      r (X.residueOverAlgebraMap K (f.base z) a) = W.residueOverAlgebraMap K z a := by
    intro a
    change IsLocalRing.ResidueField.mapEquiv (asIso (f.stalkMap z)).commRingCatIsoToRingEquiv
      (X.residueOverAlgebraMap K (f.base z) a) = W.residueOverAlgebraMap K z a
    have hun : X.residueOverAlgebraMap K (f.base z) a
        = IsLocalRing.residue _ ((X.presheaf.germ ⊤ (f.base z) trivial).hom
            (X.overAlgebraMap K ⊤ a)) := rfl
    rw [hun, IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
    change IsLocalRing.residue _ ((f.stalkMap z).hom
      ((X.presheaf.germ ⊤ (f.base z) trivial).hom (X.overAlgebraMap K ⊤ a)))
      = W.residueOverAlgebraMap K z a
    rw [hstalk a]
    rfl
  -- package as a `K`-linear equivalence and compare `finrank`s
  have hsmul : ∀ (a : K) (m : X.residueField (f.base z)), r (a • m) = a • r m := by
    intro a m
    change r (X.residueOverAlgebraMap K (f.base z) a * m)
      = W.residueOverAlgebraMap K z a * r m
    rw [map_mul, hcompat a]
  let ℓ : X.residueField (f.base z) ≃ₗ[K] W.residueField z :=
    { toFun := r, invFun := r.symm, left_inv := r.left_inv, right_inv := r.right_inv,
      map_add' := map_add r, map_smul' := hsmul }
  change Module.finrank K (W.residueField z) = Module.finrank K (X.residueField (f.base z))
  exact ℓ.finrank_eq.symm

end ResidueTransport

/-! ## The pulled tracked point system along a generic-to-generic morphism

The generic form of the E-iv-alg step-4 plumbing (`DegreeBaseFieldInvariance.lean`): the
pullback of the tracked point equations along **any** morphism `f` mapping generic point to
generic point, with the trivializing element of its presentation computed on and off the
fiber of the tracked point.  Stated for arbitrary `f` so the E-v campaign can reuse it. -/

section PulledPointSystem

variable (K : Type u) [Field K] {W X : Scheme.{u}}
  [W.Over (Spec (CommRingCat.of K))] [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X] [IsIntegral W]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]

/-- **The pulled tracked point system**: the pullback of the tracked point equations of the
closed point `x'` of `X` along a morphism `f : W ⟶ X` of integral schemes mapping generic
point to generic point, with regularity discharged by integrality
(`Scheme.LocalEquations.pullbackEqn_germ_mem_nonZeroDivisors`). -/
noncomputable def pointPullbackEquations (f : W ⟶ X)
    (hgen : f.base (genericPoint W) = genericPoint X)
    {x' : X} (hx' : x' ≠ genericPoint X) : W.LocalEquations :=
  (Scheme.pointEquations K hx' (Scheme.pointUniformizerData K hx')).pullback f
    (Scheme.LocalEquations.pullbackEqn_germ_mem_nonZeroDivisors f hgen
      (Scheme.pointEquations K hx' (Scheme.pointUniformizerData K hx')))

/-- **The trivializing unit of the pulled point system**: the pullback `f^♯` of the chosen
uniformizer at `x'`, as a unit of `K(W)`. -/
noncomputable def pointPullbackUnit (f : W ⟶ X)
    (hgen : f.base (genericPoint W) = genericPoint X)
    {x' : X} (hx' : x' ≠ genericPoint X) : W.functionFieldˣ :=
  f.functionFieldMapUnits hgen
    (Units.mk0 (uniformizer K hx') (uniformizer_ne_zero K hx'))

omit [W.Over (Spec (CommRingCat.of K))] [QuasiCompact (X ↘ Spec (CommRingCat.of K))] in
lemma coe_pointPullbackUnit (f : W ⟶ X) (hgen : f.base (genericPoint W) = genericPoint X)
    {x' : X} (hx' : x' ≠ genericPoint X) :
    (pointPullbackUnit K f hgen hx' : W.functionField)
      = (f.functionFieldMap hgen).hom (uniformizer K hx') :=
  rfl

omit [QuasiCompact (X ↘ Spec (CommRingCat.of K))] in
/-- The germ at `η` of the tracked point equation at any index equal to `x'` is the chosen
uniformizer (index-generalized form of `Scheme.germGeneric_pointEqn_self`). -/
private lemma germGeneric_pointEqn_of_eq {x' : X} (hx' : x' ≠ genericPoint X)
    (d : Scheme.PointUniformizerData K hx') {w : X} (hw : w = x')
    (hη : genericPoint X ∈ (Scheme.pointCover K hx' d).opens w) :
    (X.presheaf.germ ((Scheme.pointCover K hx' d).opens w) (genericPoint X) hη).hom
        (Scheme.pointEqn K hx' d w)
      = uniformizer K hx' := by
  subst hw
  exact Scheme.germGeneric_pointEqn_self K hx' d hη

omit [W.Over (Spec (CommRingCat.of K))] in
/-- Off the fiber of `x'`, the trivializing element of the pulled point presentation is
`1`: the second chart piece's equation is `1`, and `1` pulls back to `1`. -/
lemma pointPullbackEquations_presentation_elem_of_ne (f : W ⟶ X)
    (hgen : f.base (genericPoint W) = genericPoint X)
    {x' : X} (hx' : x' ≠ genericPoint X) {z : W} (hz : f.base z ≠ x') :
    (pointPullbackEquations K f hgen hx').presentation.elem z = 1 := by
  have hηy : genericPoint W
      ∈ f ⁻¹ᵁ (Scheme.pointEquations K hx'
          (Scheme.pointUniformizerData K hx')).cover.opens (f.base z) := by
    change f.base (genericPoint W)
      ∈ (Scheme.pointEquations K hx'
          (Scheme.pointUniformizerData K hx')).cover.opens (f.base z)
    rw [hgen]
    exact (Scheme.pointEquations K hx'
      (Scheme.pointUniformizerData K hx')).cover.genericPoint_mem_opens _
  have h1 : Scheme.LocalEquations.pullbackEqn f
      (Scheme.pointEquations K hx' (Scheme.pointUniformizerData K hx')) z = 1 := by
    have h2 : (Scheme.pointEquations K hx' (Scheme.pointUniformizerData K hx')).eqn
        (f.base z) = 1 := by
      rw [Scheme.pointEquations_eqn]
      exact Scheme.pointEqn_of_ne K hx' (Scheme.pointUniformizerData K hx') hz
    change (f.appLE _ _ le_rfl).hom
      ((Scheme.pointEquations K hx' (Scheme.pointUniformizerData K hx')).eqn
        (f.base z)) = 1
    rw [h2]
    exact map_one _
  refine Units.ext ?_
  have hval0 : ((pointPullbackEquations K f hgen hx').presentation.elem z
      : W.functionField)
      = (W.presheaf.germ
          (f ⁻¹ᵁ (Scheme.pointEquations K hx'
            (Scheme.pointUniformizerData K hx')).cover.opens (f.base z))
          (genericPoint W) hηy).hom
        (Scheme.LocalEquations.pullbackEqn f
          (Scheme.pointEquations K hx' (Scheme.pointUniformizerData K hx')) z) := rfl
  rw [hval0, h1, Units.val_one]
  exact map_one _

omit [W.Over (Spec (CommRingCat.of K))] in
/-- On the fiber of `x'`, the trivializing element of the pulled point presentation is the
pulled-back uniformizer `f^♯(t)`. -/
lemma pointPullbackEquations_presentation_elem_of_eq (f : W ⟶ X)
    (hgen : f.base (genericPoint W) = genericPoint X)
    {x' : X} (hx' : x' ≠ genericPoint X) {z : W} (hz : f.base z = x') :
    (pointPullbackEquations K f hgen hx').presentation.elem z
      = pointPullbackUnit K f hgen hx' := by
  have hηy : genericPoint W
      ∈ f ⁻¹ᵁ (Scheme.pointEquations K hx'
          (Scheme.pointUniformizerData K hx')).cover.opens (f.base z) := by
    change f.base (genericPoint W)
      ∈ (Scheme.pointEquations K hx'
          (Scheme.pointUniformizerData K hx')).cover.opens (f.base z)
    rw [hgen]
    exact (Scheme.pointEquations K hx'
      (Scheme.pointUniformizerData K hx')).cover.genericPoint_mem_opens _
  refine Units.ext ?_
  have hval0 : ((pointPullbackEquations K f hgen hx').presentation.elem z
      : W.functionField)
      = (W.presheaf.germ
          (f ⁻¹ᵁ (Scheme.pointEquations K hx'
            (Scheme.pointUniformizerData K hx')).cover.opens (f.base z))
          (genericPoint W) hηy).hom
        (Scheme.LocalEquations.pullbackEqn f
          (Scheme.pointEquations K hx' (Scheme.pointUniformizerData K hx')) z) := rfl
  have happ : Scheme.LocalEquations.pullbackEqn f
      (Scheme.pointEquations K hx' (Scheme.pointUniformizerData K hx')) z
      = (f.app _).hom
        ((Scheme.pointEquations K hx' (Scheme.pointUniformizerData K hx')).eqn
          (f.base z)) :=
    congr($(Scheme.Hom.appLE_eq_app f).hom
      ((Scheme.pointEquations K hx' (Scheme.pointUniformizerData K hx')).eqn
        (f.base z)))
  rw [hval0, coe_pointPullbackUnit, happ,
    ← f.functionFieldMap_germ hgen _
      ((Scheme.pointEquations K hx'
        (Scheme.pointUniformizerData K hx')).cover.genericPoint_mem_opens _) hηy
      ((Scheme.pointEquations K hx' (Scheme.pointUniformizerData K hx')).eqn
        (f.base z))]
  exact congrArg _
    (germGeneric_pointEqn_of_eq K hx' (Scheme.pointUniformizerData K hx') hz _)

end PulledPointSystem

/-! ## The order of the pulled uniformizer at the unique preimage point -/

section OrdPulledUnit

variable (K : Type u) [Field K] {W X : Scheme.{u}}
  [W.Over (Spec (CommRingCat.of K))] [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (W ↘ Spec (CommRingCat.of K))] [IsIntegral W]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]

/-- **The coefficient of the pulled point divisor is `1`** (the degenerate fiber
coefficient): along an isomorphism, the order at the unique fiber point `z` of the pulled
uniformizer is `+1` — `ord` transport along the stalk isomorphism, no colength. -/
lemma ordZ_pointPullbackUnit (f : W ⟶ X) [IsIso f]
    (hgen : f.base (genericPoint W) = genericPoint X)
    {z : W} (hz : z ≠ genericPoint W)
    {x' : X} (hx' : x' ≠ genericPoint X) (hzx : f.base z = x') :
    Scheme.ordZ (W ↘ Spec (CommRingCat.of K)) hz (pointPullbackUnit K f hgen hx')
      = Multiplicative.ofAdd (1 : ℤ) := by
  subst hzx
  letI := isDedekindDomain_stalk (X ↘ Spec (CommRingCat.of K)) hx'
  set d := Scheme.pointUniformizerData K hx' with hd
  have hηU : genericPoint X ∈ d.opens :=
    Scheme.genericPoint_mem_of_nonempty ⟨f.base z, d.mem⟩
  have hs0 : (X.presheaf.germ d.opens (f.base z) d.mem).hom d.sec ≠ 0 :=
    nonZeroDivisors.ne_zero (d.regular (f.base z) d.mem)
  have hgermu : (X.presheaf.germ d.opens (genericPoint X) hηU).hom d.sec
      = uniformizer K hx' := d.germ_generic
  have hord := ord_functionFieldMap_germ_of_isIso K f hgen hz hx' hηU d.mem d.sec hs0
  rw [hgermu, ord_uniformizer K hx'] at hord
  have h1 : (((Scheme.ordZ (W ↘ Spec (CommRingCat.of K)) hz
        (pointPullbackUnit K f hgen hx'))⁻¹ : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ))
      = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) := by
    rw [Scheme.coe_inv_ordZ K (pointPullbackUnit K f hgen hx') hz,
      coe_pointPullbackUnit]
    exact hord
  have h2 := congrArg Inv.inv (WithZero.coe_inj.mp h1)
  rw [inv_inv, ofAdd_neg, inv_inv] at h2
  exact h2

end OrdPulledUnit

end AlgebraicGeometry
