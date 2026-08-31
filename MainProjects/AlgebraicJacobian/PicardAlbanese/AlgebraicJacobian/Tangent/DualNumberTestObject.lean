/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Tangent.TangentCotangentCount
import AlgebraicJacobian.Tangent.TruncExpUnits

/-!
# The dual-number test object and the represented tangent kernel (W5-T1, functor layer)

The functor-of-points half of the Wave-5 tangent kit (roadmap `AJCR.w5-av.t1`):
the dual-number *test object* `Spec k[ε]` of `Over (Spec k)` with its retract
pair, and the identification of the pointed dual-number points of a
**representing** object with the `ε`-kernel of the represented functor.

Together with `Tangent/TangentIdentitySection.lean` (which computes the same
pointed dual-number points as the cotangent dual `Dual κ(e) (m_e/m_e²)`) this
is the Kleiman §5 Thm. 5.11 **representability leg**: for a functor `G`
represented by `X` and `e` a section of `X.hom`,

```
Dual κ(e) (m_e/m_e²)  ≃  T_e X  ≃  ker (G(Spec k[ε]) → G(Spec k)) .
```

Only the right-hand kernel — the *cohomological* side — is left for T3/T4 to
compute; the left-hand side is what T5 counts.

## Main declarations

* `AlgebraicGeometry.overDualNumber` — `Spec k[ε]` as an object of
  `Over (Spec k)`, the tangent test object; `overDualNumberZero` (the `ε ↦ 0`
  point) and `overDualNumberAugment` (the augmentation) form a retract pair
  (`overDualNumberZero_comp_augment`).
* `AlgebraicGeometry.overSection_ext` — two sections of a `k`-scheme through the
  same point coincide: the common point is automatically `k`-rational, so the
  stalk data of a section is the *unique* local retraction `𝒪_{X,x} → k`.
* `AlgebraicGeometry.specMap_fstRingHom_comp_eq` — a pointed dual-number point
  restricts along `ε ↦ 0` to the pointing section **itself** (upgrading the
  topological base-point condition to an equality of morphisms).
* `AlgebraicGeometry.pointedDualNumberPointsEquivRepresentableFiber` — `T_e X`
  is the *fibre* of `G(Spec k[ε]) → G(Spec k)` over the class of `e`.
* `AlgebraicGeometry.pointedDualNumberPointsEquivKer` — for a **group**-valued
  functor the fibre is a coset of the kernel, so `T_e X ≃ ker(…)`. Stated for
  `CommGrpCat`-valued `G` (the Rebuild's `pic0Functor` is commutative-group
  valued, unlike the sibling's additive spelling), so the kernel is the
  multiplicative `G.map`-kernel.

## Provenance (W5-T1 port, cross-project)

The generic content is ported from `Algebraic-Jacobian-Challenge`,
`AlgebraicJacobian/Picard/Pic0DualNumberCocycle.lean` §§0–3 (sorry-free); see
inbox `I-0495` overlap #2. Two deliberate deviations from the source:

* the kernel statement is phrased for `CommGrpCat`-valued functors and a
  *multiplicative* kernel, because the Rebuild's `pic0Functor` lands in
  `CommGrpCat` (`Picard/Pic0Functor.lean`) where the sibling's `picSharp` lands
  in `AddCommGrpCat`;
* the `k`-linear (Mumford `ε ↦ aε`) scaling layer of the source's §4/§5 is
  **not** ported here. Under the w5-worksheet D6 *scalar-identity-first*
  discipline the Wave-5 count is done cocycle-side, where linearity is honest
  module structure, so the scaling action — whose scalar distributivity
  `(a+b)•x` is the named open gap of the source — is never needed on this side.
  Porting it would import exactly that gap for no consumer.

Reference: Kleiman, "The Picard scheme", §5 Thm. 5.11 (arXiv:math/0504020);
Mumford, "Abelian varieties", §II.4.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u v

open CategoryTheory IsLocalRing

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-! ## §1. Uniqueness of local retractions to the base field -/

/-- **Uniqueness of local retractions at a rational point.** Two *local* ring
homomorphisms `φ, ψ : R →+* k` retracting a given `ι : k →+* R` agree, as soon
as `k → κ(R)` is surjective: every `r : R` is congruent mod `m` to some `ι c`,
a local hom kills `m`, so both send `r` to that `c`. -/
theorem IsLocalRing.ringHom_ext_of_surjective_residue_comp
    {R : Type v} [CommRing R] [IsLocalRing R]
    {ι : k →+* R} (hres : Function.Surjective ((residue R).comp ι))
    {φ ψ : R →+* k} (hφl : IsLocalHom φ) (hψl : IsLocalHom ψ)
    (hφ : φ.comp ι = RingHom.id k) (hψ : ψ.comp ι = RingHom.id k) :
    φ = ψ := by
  have key : ∀ χ : R →+* k, IsLocalHom χ → χ.comp ι = RingHom.id k →
      ∀ (r : R) (c : k), residue R r = residue R (ι c) → χ r = c := by
    intro χ hχ hχ1 r c hc
    have hmem : r - ι c ∈ maximalIdeal R := by
      rw [← residue_eq_zero_iff, map_sub, hc, sub_self]
    have h0 : χ (r - ι c) = 0 := by
      by_contra hne
      have hu : IsUnit (χ (r - ι c)) := isUnit_iff_ne_zero.mpr hne
      exact mem_nonunits_iff.mp ((mem_maximalIdeal _).mp hmem) (hχ.map_nonunit _ hu)
    have hc' : χ (ι c) = c := by
      have := DFunLike.congr_fun hχ1 c
      simpa using this
    have := map_sub χ r (ι c)
    rw [h0, hc'] at this
    exact sub_eq_zero.mp this.symm
  refine RingHom.ext fun r => ?_
  obtain ⟨c, hc⟩ := hres (residue R r)
  have hc' : residue R r = residue R (ι c) := by
    rw [← hc]; rfl
  rw [key φ hφl hφ r c hc', key ψ hψl hψ r c hc']

/-! ## §2. The dual-number test object of `Over (Spec k)` and its retract pair -/

/-- The composite `Spec k → Spec k[ε] → Spec k` of the `ε ↦ 0` point with the
augmentation is the identity: on rings, `fst ∘ inl = id`. -/
lemma specMap_fstRingHom_comp (k : Type u) [Field k] :
    Spec.map (CommRingCat.ofHom (TruncExpCech.fstRingHom (R := k))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))
      = 𝟙 (Spec (CommRingCat.of k)) := by
  have h : CommRingCat.ofHom (algebraMap k (DualNumber k)) ≫
      CommRingCat.ofHom (TruncExpCech.fstRingHom (R := k)) = 𝟙 (CommRingCat.of k) := by
    ext c
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [← Spec.map_comp, h, Spec.map_id]

/-- **The dual-number test object** `Spec k[ε]` as an object of `Over (Spec k)`.
Its pointed `X`-valued points at a section `e` of a `k`-scheme `X` form the
Zariski tangent space `T_e X` (Mumford, "Abelian varieties", §II.4). -/
noncomputable def overDualNumber (k : Type u) [Field k] :
    Over (Spec (CommRingCat.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))

/-- **The `ε ↦ 0` point** `Spec k ⟶ Spec k[ε]`, as a morphism in
`Over (Spec k)` out of the trivial over-object. Restricting a tangent vector
along it recovers the underlying point. -/
noncomputable def overDualNumberZero (k : Type u) [Field k] :
    Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ overDualNumber k :=
  Over.homMk (Spec.map (CommRingCat.ofHom (TruncExpCech.fstRingHom (R := k))))
    (specMap_fstRingHom_comp k)

/-- **The augmentation** `Spec k[ε] ⟶ Spec k`, as a morphism in `Over (Spec k)`
into the trivial over-object. Composition with it produces the "constant"
tangent vectors. -/
noncomputable def overDualNumberAugment (k : Type u) [Field k] :
    overDualNumber k ⟶ Over.mk (𝟙 (Spec (CommRingCat.of k))) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))
    (Category.comp_id _)

/-- The `ε ↦ 0` point and the augmentation form a retract pair. -/
lemma overDualNumberZero_comp_augment (k : Type u) [Field k] :
    overDualNumberZero k ≫ overDualNumberAugment k
      = 𝟙 (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
  apply Over.OverMorphism.ext
  exact specMap_fstRingHom_comp k

/-! ## §3. Sections through a common point coincide -/

/-- **Two sections of a `k`-scheme through the same point coincide.** For a
scheme `X` over `Spec k` and sections `e₁, e₂` of the structure morphism with
`e₁(*) = e₂(*)`, already `e₁ = e₂`: the common image point is `k`-rational
(`bijective_algebraMap_residueField_of_section`), a morphism `Spec k ⟶ X` at a
fixed point is determined by its stalk data (`specToEquivOfLocalRingAt`), and
the stalk data of a section is a *local retraction* `𝒪_{X,x} → k` of the
structure homomorphism — unique at a rational point
(`IsLocalRing.ringHom_ext_of_surjective_residue_comp`). -/
theorem overSection_ext (X : Over (Spec (CommRingCat.of k)))
    {e₁ e₂ : Spec (CommRingCat.of k) ⟶ X.left}
    (h₁ : e₁ ≫ X.hom = 𝟙 (Spec (CommRingCat.of k)))
    (h₂ : e₂ ≫ X.hom = 𝟙 (Spec (CommRingCat.of k)))
    (hbase : e₁.base default = e₂.base default) :
    e₁ = e₂ := by
  haveI : IsLocalRing ↥(CommRingCat.of k) := inferInstanceAs (IsLocalRing k)
  haveI : Subsingleton ↥(Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  set x : X.left := e₂.base (closedPoint ↥(CommRingCat.of k)) with hxdef
  have hb₂ : e₂.base (closedPoint ↥(CommRingCat.of k)) = x := hxdef.symm
  have hb₁ : e₁.base (closedPoint ↥(CommRingCat.of k)) = x :=
    (congrArg e₁.base (Subsingleton.elim _ _)).trans <|
      hbase.trans <| (congrArg e₂.base (Subsingleton.elim _ _)).trans hb₂
  have hres : Function.Surjective
      (algebraMap k (ResidueField (X.left.presheaf.stalk x))) :=
    (bijective_algebraMap_residueField_of_section X h₂
      ((congrArg e₂.base (Subsingleton.elim _ _)).trans hb₂)).2
  have hres' : Function.Surjective
      ((residue (X.left.presheaf.stalk x)).comp (stalkStructureHom X.hom x).hom) := by
    intro y
    obtain ⟨c, hc⟩ := hres y
    refine ⟨c, ?_⟩
    have hra : residue (X.left.presheaf.stalk x)
        (algebraMap k (X.left.presheaf.stalk x) c)
          = algebraMap k (ResidueField (X.left.presheaf.stalk x)) c :=
      residue_algebraMap c
    rw [RingHom.comp_apply, ← algebraMap_overStalkAlgebra X x, hra, hc]
  let E := specToEquivOfLocalRingAt X.left (CommRingCat.of k) x
  have hE : E ⟨e₁, hb₁⟩ = E ⟨e₂, hb₂⟩ := by
    apply Subtype.ext
    have hv₁ : (E ⟨e₁, hb₁⟩).1
        = (X.left.presheaf.stalkCongr (Inseparable.of_eq hb₁.symm)).hom ≫
            Scheme.stalkClosedPointTo e₁ := rfl
    have hv₂ : (E ⟨e₂, hb₂⟩).1
        = (X.left.presheaf.stalkCongr (Inseparable.of_eq hb₂.symm)).hom ≫
            Scheme.stalkClosedPointTo e₂ := rfl
    rw [hv₁, hv₂]
    haveI : IsLocalHom ((X.left.presheaf.stalkCongr
        (Inseparable.of_eq hb₁.symm)).hom).hom := isLocalHom_of_isIso _
    haveI : IsLocalHom ((X.left.presheaf.stalkCongr
        (Inseparable.of_eq hb₂.symm)).hom).hom := isLocalHom_of_isIso _
    have hc₁ : stalkStructureHom X.hom x ≫
        (X.left.presheaf.stalkCongr (Inseparable.of_eq hb₁.symm)).hom ≫
          Scheme.stalkClosedPointTo e₁ = 𝟙 (CommRingCat.of k) :=
      (comp_eq_spec_iff_of_base_eq X.hom hb₁ (𝟙 (CommRingCat.of k))).mp
        (by rw [Spec.map_id]; exact h₁)
    have hc₂ : stalkStructureHom X.hom x ≫
        (X.left.presheaf.stalkCongr (Inseparable.of_eq hb₂.symm)).hom ≫
          Scheme.stalkClosedPointTo e₂ = 𝟙 (CommRingCat.of k) :=
      (comp_eq_spec_iff_of_base_eq X.hom hb₂ (𝟙 (CommRingCat.of k))).mp
        (by rw [Spec.map_id]; exact h₂)
    apply CommRingCat.hom_ext
    refine IsLocalRing.ringHom_ext_of_surjective_residue_comp hres'
      (CommRingCat.isLocalHom_comp _ _) (CommRingCat.isLocalHom_comp _ _) ?_ ?_
    · have := congrArg CommRingCat.Hom.hom hc₁
      simpa using this
    · have := congrArg CommRingCat.Hom.hom hc₂
      simpa using this
  exact congrArg Subtype.val (E.injective hE)

/-- **A pointed dual-number point restricts to the pointing section.** For a
section `e` of a `k`-scheme `X` and a dual-number point `g` of `X` over
`Spec k` landing at `e(*)`, the restriction of `g` along the `ε ↦ 0` point is
`e` itself — a scheme-morphism-level upgrade of the topological base-point
condition, valid because sections through a common (automatically `k`-rational)
point coincide (`overSection_ext`). -/
theorem specMap_fstRingHom_comp_eq (X : Over (Spec (CommRingCat.of k)))
    {e : Spec (CommRingCat.of k) ⟶ X.left}
    (he : e ≫ X.hom = 𝟙 (Spec (CommRingCat.of k)))
    {g : Spec (CommRingCat.of (DualNumber k)) ⟶ X.left}
    (hg : g ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))
    (hbase : g.base (closedPoint (DualNumber k)) = e.base default) :
    Spec.map (CommRingCat.ofHom (TruncExpCech.fstRingHom (R := k))) ≫ g = e := by
  haveI : Subsingleton ↥(Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  haveI : Subsingleton ↥(Spec (CommRingCat.of (DualNumber k))) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum (DualNumber k)))
  refine overSection_ext X ?_ he ?_
  · rw [Category.assoc, hg, specMap_fstRingHom_comp]
  · have h0 : (Spec.map (CommRingCat.ofHom
        (TruncExpCech.fstRingHom (R := k)))).base default
          = closedPoint (DualNumber k) := Subsingleton.elim _ _
    rw [Scheme.Hom.comp_apply, h0, hbase]

/-! ## §4. The fibre and kernel descriptions of the tangent space

The representability leg proper. `pointedDualNumberPoints X e` below is the
functor-of-points tangent space: dual-number points of `X` over `Spec k` whose
closed point lands at `e(*)`. -/

/-- **Pointed dual-number points of `X` at `e`, over `Spec k`.** The
`k[ε]`-valued points of `X` lying over `Spec k[ε]` and landing at `e` — the
functor-of-points model of the Zariski tangent space `T_e X`. A named
restatement of the anonymous subtype the equivalences of
`Tangent/TangentIdentitySection.lean` target, kept for readability at the call
sites. -/
def pointedDualNumberPoints (X : Over (Spec (CommRingCat.of k)))
    (e : Spec (CommRingCat.of k) ⟶ X.left) :=
  {g : Spec (CommRingCat.of (DualNumber k)) ⟶ X.left //
      g ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))
        ∧ g.base (closedPoint (DualNumber k)) = e.base default}

/-- **The tangent space of a represented functor, as a fibre.** Let `F` be a
functor on `Over (Spec k)` represented by a `k`-scheme `X`, and `e` a section of
the structure morphism. Composition with the representing natural bijection
identifies `T_e X` with the fibre of the restriction map
`F(Spec k[ε]) → F(Spec k)` (along the `ε ↦ 0` point) over the class of `e`. The
base-point condition transports to the fibre condition by
`specMap_fstRingHom_comp_eq` (sections through a common rational point
coincide). -/
noncomputable def pointedDualNumberPointsEquivRepresentableFiber
    (X : Over (Spec (CommRingCat.of k)))
    {F : (Over (Spec (CommRingCat.of k)))ᵒᵖ ⥤ Type v}
    (rep : F.RepresentableBy X)
    {e : Spec (CommRingCat.of k) ⟶ X.left}
    (he : e ≫ X.hom = 𝟙 (Spec (CommRingCat.of k))) :
    pointedDualNumberPoints X e
      ≃ {a : F.obj (Opposite.op (overDualNumber k)) //
          F.map (overDualNumberZero k).op a
            = rep.homEquiv
                (Over.homMk e he : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X)} where
  toFun g :=
    ⟨rep.homEquiv (Over.homMk g.1 g.2.1 : overDualNumber k ⟶ X), by
      rw [← rep.homEquiv_comp]
      exact DFunLike.congr_arg rep.homEquiv (Over.OverMorphism.ext
        (specMap_fstRingHom_comp_eq X he g.2.1 g.2.2))⟩
  invFun a :=
    ⟨(rep.homEquiv.symm a.1).left,
      Over.w (rep.homEquiv.symm a.1),
      by
        haveI : Subsingleton ↥(Spec (CommRingCat.of (DualNumber k))) :=
          inferInstanceAs (Subsingleton (PrimeSpectrum (DualNumber k)))
        haveI : Subsingleton ↥(overDualNumber k).left :=
          inferInstanceAs (Subsingleton (PrimeSpectrum (DualNumber k)))
        have hcomp : overDualNumberZero k ≫ rep.homEquiv.symm a.1
            = (Over.homMk e he : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X) := by
          apply rep.homEquiv.injective
          rw [rep.homEquiv_comp, Equiv.apply_symm_apply]
          exact a.2
        have hleft : Spec.map (CommRingCat.ofHom (TruncExpCech.fstRingHom (R := k)))
            ≫ (rep.homEquiv.symm a.1).left = e :=
          congrArg CategoryTheory.CommaMorphism.left hcomp
        calc (rep.homEquiv.symm a.1).left.base (closedPoint (DualNumber k))
            = (Spec.map (CommRingCat.ofHom (TruncExpCech.fstRingHom (R := k)))
                ≫ (rep.homEquiv.symm a.1).left).base default := by
              rw [Scheme.Hom.comp_apply]
              exact congrArg (rep.homEquiv.symm a.1).left.base
                (Subsingleton.elim _ _)
          _ = e.base default := by rw [hleft]⟩
  left_inv g := Subtype.ext
    (congrArg CategoryTheory.CommaMorphism.left
      (rep.homEquiv.symm_apply_apply
        (Over.homMk g.1 g.2.1 : overDualNumber k ⟶ X)))
  right_inv a := Subtype.ext (by
    have h : ∀ w : (rep.homEquiv.symm a.1).left ≫ X.hom = (overDualNumber k).hom,
        rep.homEquiv (Over.homMk (rep.homEquiv.symm a.1).left w) = a.1 := by
      intro w
      rw [show Over.homMk (rep.homEquiv.symm a.1).left w = rep.homEquiv.symm a.1 from
        Over.OverMorphism.ext rfl, Equiv.apply_symm_apply]
    exact h _)

/-- **Fibres of a group homomorphism translate onto the kernel.** For
`f : A →* B` and a base point `a₀`, dividing by `a₀` identifies the fibre of `f`
through `f a₀` with `ker f`. This is the normalisation step turning the fibre
description of the tangent space into the kernel description of Kleiman §5
Thm. 5.11. (Primed: mathlib's `MonoidHom.fiberEquivKer` states the same content
on the carriers `f ⁻¹' {f a} ≃ f.ker`; this variant is phrased on the *equation
subtypes* that `pointedDualNumberPointsEquivRepresentableFiber` produces.) -/
def MonoidHom.fiberEquivKer' {A : Type u} {B : Type v}
    [CommGroup A] [CommGroup B] (f : A →* B) (a₀ : A) :
    {a : A // f a = f a₀} ≃ {a : A // f a = 1} where
  toFun a := ⟨a.1 / a₀, by rw [map_div, a.2, div_self']⟩
  invFun a := ⟨a.1 * a₀, by rw [map_mul, a.2, one_mul]⟩
  left_inv a := Subtype.ext (by simp)
  right_inv a := Subtype.ext (by simp)

/-- **The tangent space of a representably group-valued functor, as a kernel**
(Kleiman §5 Thm. 5.11, representability leg). Let `G` be a `CommGrpCat`-valued
functor on `Over (Spec k)` whose set-valued shadow is represented by a
`k`-scheme `X`, and `e` a section of the structure morphism. Then `T_e X`
bijects with the **kernel** of the restriction homomorphism
`G(Spec k[ε]) →* G(Spec k)`.

The fibre over the class of `e` is a coset of that kernel, because `e`'s own
class is hit by the *constant* tangent vector `augment ≫ e` — the retract-pair
identity `overDualNumberZero_comp_augment` is exactly what says so.

⚠ This is a bijection of **sets**. It does not by itself transport `finrank`: a
bare `Equiv` does not determine dimension. The `k`-linearity bookkeeping is
deliberately *not* done here — under the w5-worksheet D6 scalar-identity-first
discipline it is done cocycle-side (T2/T3), where linearity is honest module
structure, and enters the count through
`nonempty_cotangentSpaceAddEquiv_of_finrank_eq`. -/
noncomputable def pointedDualNumberPointsEquivKer
    (X : Over (Spec (CommRingCat.of k)))
    (G : (Over (Spec (CommRingCat.of k)))ᵒᵖ ⥤ CommGrpCat.{v})
    (rep : (G ⋙ CategoryTheory.forget CommGrpCat.{v}).RepresentableBy X)
    {e : Spec (CommRingCat.of k) ⟶ X.left}
    (he : e ≫ X.hom = 𝟙 (Spec (CommRingCat.of k))) :
    pointedDualNumberPoints X e
      ≃ {a : G.obj (Opposite.op (overDualNumber k)) //
          (G.map (overDualNumberZero k).op).hom a = 1} := by
  -- the constant tangent vector at `e`, whose restriction is the class of `e`
  have ha₀ : (G.map (overDualNumberZero k).op).hom
      (rep.homEquiv (overDualNumberAugment k ≫
        (Over.homMk e he : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X)))
        = rep.homEquiv (Over.homMk e he : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X) := by
    have h := (rep.homEquiv_comp (overDualNumberZero k)
      (overDualNumberAugment k ≫
        (Over.homMk e he : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X))).symm
    rwa [← Category.assoc, overDualNumberZero_comp_augment, Category.id_comp] at h
  exact (pointedDualNumberPointsEquivRepresentableFiber X rep he).trans <|
    (Equiv.subtypeEquivRight fun a => by rw [← ha₀]; exact Iff.rfl).trans
      (MonoidHom.fiberEquivKer' (G.map (overDualNumberZero k).op).hom
        (rep.homEquiv (overDualNumberAugment k ≫
          (Over.homMk e he : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X))))

end AlgebraicGeometry
