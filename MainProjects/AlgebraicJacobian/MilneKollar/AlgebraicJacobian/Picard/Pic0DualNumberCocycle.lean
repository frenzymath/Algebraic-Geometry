/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0TangentSpace
import AlgebraicJacobian.Picard.DualNumberUnits

/-!
# Tangent-space endgame: the representability leg of Kleiman §5 Thm 5.11

Leg (iii) of the Kleiman §5 Thm.~5.11 tangent-space computation for
`Pic⁰_{C/k}` (`Pic0.tangentSpaceIso`, `Picard/Pic0AbelianVariety.lean`): for a
functor `F` on `Over (Spec k)` **represented by** a `k`-scheme `X` and a
section `e` of the structure morphism, the pointed dual-number points of `X`
at `e` — the functor-of-points Zariski tangent space `T_e X` — are identified,
through the representing natural bijection, with the **fiber** of
`F(Spec k[ε]) → F(Spec k)` (restriction along the `ε ↦ 0` closed point) over
the class of `e`; when `F` is the set-valued shadow of a functor in abelian
groups, translation by the constant dual-number point over `e` normalises the
fiber to the **kernel** of `F(Spec k[ε]) →+ F(Spec k)`.

Applied to `F = Pic^♯_{C/k}` (`PicScheme.picSharp`, whose representing scheme
is the `[HasPicScheme C]`-gated `PicScheme C`), this is exactly Kleiman's
identification `T_e Pic_{C/k} = ker(Pic(C ×_k Spec k[ε]) → Pic(C))` — see
`Pic0.cotangentSpaceDual_equiv_relPicKernel` in
`Picard/Pic0AbelianVariety.lean`. The remaining legs of Thm 5.11 (the
truncated-exponential Čech-cocycle computation of that kernel on a 2-affine
cover, with the `k`-linearity bookkeeping) will live here as well — whence
the file name.

## Main declarations

- `AddMonoidHom.fiberEquivKer'` — the fiber of an additive-group homomorphism
  over the image of a point translates onto the kernel.
- `IsLocalRing.ringHom_ext_of_surjective_residue_comp` — **uniqueness of
  local retractions to the base field at a rational point**: two local ring
  homomorphisms `R →+* k` retracting a given `ι : k →+* R` with `k ↠ κ(R)`
  agree.
- `AlgebraicGeometry.overDualNumber`, `overDualNumberZero`,
  `overDualNumberAugment` — the dual-number object `Spec k[ε]` of
  `Over (Spec k)` with its `ε ↦ 0` point and its augmentation, a retract
  pair (`overDualNumberZero_comp_augment`).
- `AlgebraicGeometry.overSection_ext` — two sections of a `k`-scheme through
  the same point coincide (the point is `k`-rational, so the stalk data of a
  section is the *unique* local retraction `𝒪_{X,x} → k`).
- `AlgebraicGeometry.specMap_fstRingHom_comp_eq` — a pointed dual-number
  point restricts along `ε ↦ 0` to the pointing section itself.
- `AlgebraicGeometry.pointedDualNumberPointsEquivRepresentableFiber` — the
  fiber description of `T_e X` for represented functors.
- `AlgebraicGeometry.pointedDualNumberPointsEquivAddKernel` — the kernel
  description for representably group-valued functors.
- `DualNumber.scaleRingHom`, `AlgebraicGeometry.overDualNumberScale` — the
  Mumford `ε ↦ aε` scaling of `k[ε]` resp. of the dual-number object of
  `Over (Spec k)`, with its retract-pair compatibilities.
- `AlgebraicGeometry.relPicKernelSMul` — the induced multiplicative-monoid
  action of `k` on the dual-number kernel of a group-valued functor (the
  scalar multiplication of the Kleiman/Mumford `k`-module structure on
  `T_e`; distributivity in the scalar is deferred to the cocycle leg).
- §6 (wave-5 W12-cocycle): the **two-chart Čech unit-cocycle engine**, the
  pure-algebra heart of the Kleiman §5 Thm 5.11 cocycle leg.
  `DualNumber.cechCoboundaryUnits ρ₁ ρ₂` is the coboundary subgroup
  `im(ρ₁ˣ) · im(ρ₂ˣ) ≤ Bˣ` of a two-chart datum `ρᵢ : Aᵢ →+* B` (think
  `Aᵢ = Γ(Uᵢ, 𝒪)`, `B = Γ(U₁ ⊓ U₂, 𝒪)`), so `Bˣ ⧸ cechCoboundaryUnits` is
  the two-cover Čech `Ȟ¹` of units — the two-chart Picard group.
  `DualNumber.cechUnitsReduction` is its reduction mod `ε`, and
  `DualNumber.truncExpCechKernelAddEquiv` computes its kernel by the
  truncated exponential:
  `B ⧸ (ρ₁(A₁) + ρ₂(A₂)) ≃+ ker(Ȟ¹ˣ(B[ε]) → Ȟ¹ˣ(B))` — the algebra layer of
  `ker(Pic(C_ε) → Pic(C)) ≅ H¹(C, 𝒪_C)`, with target quotient matching the
  `AffineCoverMVSquare.H1Cok` carrier. Mumford-scaling equivariance is
  `DualNumber.unitsScale_mk_truncExpUnit` +
  `DualNumber.cechCoboundaryUnits_le_comap_unitsScale`.
- §7 (wave-5 W12-cocycle): **dual numbers under base change**,
  `DualNumber.baseChangeAlgEquiv : A ⊗[k] k[ε] ≃ₐ[A] A[ε]` with the explicit
  inverse `x ↦ x.fst ⊗ 1 + x.snd ⊗ ε` — the algebra core of the
  chart-sections identification `Γ(V × Spec k[ε], 𝒪) ≅ Γ(V, 𝒪)[ε]` for
  affine `V` (substrate piece (i); compose with Mathlib's `pullbackSpecIso`).

## References

Kleiman, "The Picard scheme", §5, proof of Thm.~5.11 (arXiv:math/0504020);
Mumford, "Abelian varieties", §II.4 (the `Spec k[ε]`-point description of the
tangent space of a functor).

Blueprint: `blueprint/src/chapters/Picard_Pic0AbelianVariety.tex`,
§ `sec:pic0_tangent_space`.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u v w

open CategoryTheory IsLocalRing

/-- **Fibers of an additive-group homomorphism translate onto the kernel.**
For `f : A →+ B` and a base point `a₀ : A`, subtracting `a₀` identifies the
fiber of `f` through `f a₀` with `ker f`. This is the normalisation step
turning the fiber description of the dual-number points of a represented
group functor (`pointedDualNumberPointsEquivRepresentableFiber` below) into
the kernel description of Kleiman §5 Thm.~5.11. (Primed: mathlib's
`AddMonoidHom.fiberEquivKer` states the same content on the carriers
`f ⁻¹' {f a} ≃ f.ker`; this variant is phrased on the equation subtypes the
represented-fiber equivalence produces.) -/
def AddMonoidHom.fiberEquivKer' {A : Type u} {B : Type v}
    [AddCommGroup A] [AddCommGroup B] (f : A →+ B) (a₀ : A) :
    {a : A // f a = f a₀} ≃ {a : A // f a = 0} where
  toFun a := ⟨a.1 - a₀, by rw [map_sub, a.2, sub_self]⟩
  invFun a := ⟨a.1 + a₀, by rw [map_add, a.2, zero_add]⟩
  left_inv a := Subtype.ext (by simp)
  right_inv a := Subtype.ext (by simp)

/-- **Uniqueness of local retractions to the base field at a rational
point.** Let `R` be a local ring, `k` a field, `ι : k →+* R` a homomorphism
such that `k → R → κ(R)` is surjective (a "rational point"). Then two *local*
ring homomorphisms `φ ψ : R →+* k` with `φ ∘ ι = ψ ∘ ι = id` are equal:
locality forces both to kill the maximal ideal, and by rationality every
`r : R` is congruent to a constant `ι c` mod `m`, so `φ r = c = ψ r`.

This is the algebraic heart of `AlgebraicGeometry.overSection_ext` below (two
sections of a `k`-scheme through one point coincide). Stated with an explicit
`ι` rather than `[Algebra k R]` so that call sites with categorical carriers
(`CommRingCat` stalks) need no instance bookkeeping. -/
theorem IsLocalRing.ringHom_ext_of_surjective_residue_comp
    {k : Type u} {R : Type v} [Field k] [CommRing R] [IsLocalRing R]
    {ι : k →+* R} (hres : Function.Surjective ((residue R).comp ι))
    {φ ψ : R →+* k} (hφl : IsLocalHom φ) (hψl : IsLocalHom ψ)
    (hφ : φ.comp ι = RingHom.id k) (hψ : ψ.comp ι = RingHom.id k) :
    φ = ψ := by
  have key : ∀ (χ : R →+* k), IsLocalHom χ → χ.comp ι = RingHom.id k →
      ∀ (r : R) (c : k), residue R r = residue R (ι c) → χ r = c := by
    intro χ hχ hχ1 r c hc
    have hmem : r - ι c ∈ maximalIdeal R := by
      rw [← residue_eq_zero_iff, map_sub, hc, sub_self]
    have h0 : χ (r - ι c) = 0 := by
      by_contra hne
      exact (mem_maximalIdeal _).mp hmem
        (hχ.map_nonunit _ (isUnit_iff_ne_zero.mpr hne))
    have hr : χ r = χ (r - ι c) + χ (ι c) := by
      rw [← map_add, sub_add_cancel]
    rw [hr, h0, zero_add]
    exact RingHom.congr_fun hχ1 c
  ext r
  obtain ⟨c, hc⟩ := hres (residue R r)
  rw [key φ hφl hφ r c hc.symm, key ψ hψl hψ r c hc.symm]

namespace DualNumber

open TrivSqZeroExt

variable {R : Type w} [CommRing R]

/-- **The `ε ↦ aε` scaling of the dual numbers**: `TrivSqZeroExt.map` of
scalar multiplication by `a` on the infinitesimal part, as a ring
homomorphism `R[ε] →+* R[ε]`, `r + m ε ↦ r + (a m) ε`. Mumford's `k`-module
structure on the tangent space `T_e F` of a functor at a rational point
scales tangent vectors by functoriality along it ("Abelian varieties",
§II.4); the scheme-level upgrade is `AlgebraicGeometry.overDualNumberScale`
below. -/
def scaleRingHom (a : R) : R[ε] →+* R[ε] :=
  (TrivSqZeroExt.map (a • (LinearMap.id : R →ₗ[R] R))).toRingHom

@[simp]
theorem fst_scaleRingHom (a : R) (x : R[ε]) : (scaleRingHom a x).fst = x.fst := by
  simp [scaleRingHom]

@[simp]
theorem snd_scaleRingHom (a : R) (x : R[ε]) : (scaleRingHom a x).snd = a * x.snd := by
  simp [scaleRingHom]

/-- Scalings compose multiplicatively: `(ε ↦ aε) ∘ (ε ↦ bε) = (ε ↦ (ab)ε)`. -/
theorem scaleRingHom_comp_scaleRingHom (a b : R) :
    (scaleRingHom a).comp (scaleRingHom b) = scaleRingHom (a * b) :=
  RingHom.ext fun x => TrivSqZeroExt.ext (by simp) (by simp [mul_assoc])

/-- Scaling by `1` is the identity. -/
theorem scaleRingHom_one : scaleRingHom (1 : R) = RingHom.id R[ε] :=
  RingHom.ext fun x => TrivSqZeroExt.ext (by simp) (by simp)

/-- Scaling by `0` is the retract `R[ε] → R → R[ε]` (kill `ε`, include
back). -/
theorem scaleRingHom_zero :
    scaleRingHom (0 : R) = (algebraMap R R[ε]).comp (fstRingHom (R := R)) :=
  RingHom.ext fun x => TrivSqZeroExt.ext
    (by simp [TrivSqZeroExt.algebraMap_eq_inl])
    (by simp [TrivSqZeroExt.algebraMap_eq_inl])

/-- The scaling fixes the constants: `scaleRingHom a ∘ inl = inl`. -/
theorem scaleRingHom_comp_algebraMap (a : R) :
    (scaleRingHom a).comp (algebraMap R R[ε]) = algebraMap R R[ε] :=
  RingHom.ext fun c => TrivSqZeroExt.ext
    (by simp [TrivSqZeroExt.algebraMap_eq_inl])
    (by simp [TrivSqZeroExt.algebraMap_eq_inl])

/-- The scaling commutes with reduction mod `ε`: `fst ∘ scaleRingHom a = fst`. -/
theorem fstRingHom_comp_scaleRingHom (a : R) :
    (fstRingHom (R := R)).comp (scaleRingHom a) = fstRingHom (R := R) :=
  RingHom.ext fun x => by simp

end DualNumber

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-! ## §1. The dual-number object of `Over (Spec k)` and its retract pair -/

/-- The composite `Spec k → Spec k[ε] → Spec k` of the `ε ↦ 0` point with the
augmentation is the identity: on rings, `fst ∘ inl = id`. -/
lemma specMap_fstRingHom_comp (k : Type u) [Field k] :
    Spec.map (CommRingCat.ofHom (DualNumber.fstRingHom (R := k))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))
      = 𝟙 (Spec (CommRingCat.of k)) := by
  have h : CommRingCat.ofHom (algebraMap k (DualNumber k)) ≫
      CommRingCat.ofHom (DualNumber.fstRingHom (R := k)) = 𝟙 (CommRingCat.of k) := by
    ext c
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [← Spec.map_comp, h, Spec.map_id]

/-- **The dual-number object** `Spec k[ε]` as an object of `Over (Spec k)`,
via the structure map `Spec` of `k → k[ε]`. Its pointed `X`-valued points at
a section `e` of a `k`-scheme `X` form the Zariski tangent space `T_e X`
(Mumford, "Abelian varieties", §II.4). -/
noncomputable def overDualNumber (k : Type u) [Field k] :
    Over (Spec (CommRingCat.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))

/-- **The `ε ↦ 0` point** `Spec k ⟶ Spec k[ε]` of the dual-number object, as
a morphism in `Over (Spec k)` out of the trivial over-object. Restriction of
a tangent vector along it recovers the underlying point. -/
noncomputable def overDualNumberZero (k : Type u) [Field k] :
    Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ overDualNumber k :=
  Over.homMk (Spec.map (CommRingCat.ofHom (DualNumber.fstRingHom (R := k))))
    (specMap_fstRingHom_comp k)

/-- **The augmentation** `Spec k[ε] ⟶ Spec k` of the dual-number object, as a
morphism in `Over (Spec k)` into the trivial over-object. Composition with it
produces "constant" tangent vectors. -/
noncomputable def overDualNumberAugment (k : Type u) [Field k] :
    overDualNumber k ⟶ Over.mk (𝟙 (Spec (CommRingCat.of k))) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))
    (Category.comp_id _)

/-- The `ε ↦ 0` point and the augmentation form a retract pair:
`Spec k → Spec k[ε] → Spec k` is the identity of the trivial over-object. -/
lemma overDualNumberZero_comp_augment (k : Type u) [Field k] :
    overDualNumberZero k ≫ overDualNumberAugment k
      = 𝟙 (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
  apply Over.OverMorphism.ext
  exact specMap_fstRingHom_comp k

/-! ## §2. Sections through a common point coincide -/

/-- **Two sections of a `k`-scheme through the same point coincide.** For a
scheme `X` over `Spec k` and sections `e₁, e₂` of the structure morphism with
`e₁(*) = e₂(*)`, already `e₁ = e₂`: the common image point is `k`-rational
(`bijective_algebraMap_residueField_of_section`), a morphism `Spec k ⟶ X` at
a fixed point is determined by its stalk data (`specToEquivOfLocalRingAt`),
and the stalk data of a section is a *local retraction* `𝒪_{X,x} → k` of the
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
  -- the common image point is `k`-rational
  have hres : Function.Surjective
      (algebraMap k (ResidueField (X.left.presheaf.stalk x))) :=
    (bijective_algebraMap_residueField_of_section X h₂
      ((congrArg e₂.base (Subsingleton.elim _ _)).trans hb₂)).2
  -- surjectivity of `k → 𝒪_{X,x} → κ(x)` with the explicit structure hom
  have hres' : Function.Surjective
      ((residue (X.left.presheaf.stalk x)).comp (stalkStructureHom X.hom x).hom) := by
    intro y
    obtain ⟨c, hc⟩ := hres y
    refine ⟨c, ?_⟩
    have : residue (X.left.presheaf.stalk x)
        (algebraMap k (X.left.presheaf.stalk x) c)
          = algebraMap k (ResidueField (X.left.presheaf.stalk x)) c :=
      residue_algebraMap c
    rw [RingHom.comp_apply, ← algebraMap_overStalkAlgebra X x, this, hc]
  -- pass to stalk data
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
    -- both stalk data are local retractions of the structure homomorphism
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
condition, valid because sections through a common (automatically
`k`-rational) point coincide (`overSection_ext`). -/
theorem specMap_fstRingHom_comp_eq (X : Over (Spec (CommRingCat.of k)))
    {e : Spec (CommRingCat.of k) ⟶ X.left}
    (he : e ≫ X.hom = 𝟙 (Spec (CommRingCat.of k)))
    {g : Spec (CommRingCat.of (DualNumber k)) ⟶ X.left}
    (hg : g ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))
    (hbase : g.base (closedPoint (DualNumber k)) = e.base default) :
    Spec.map (CommRingCat.ofHom (DualNumber.fstRingHom (R := k))) ≫ g = e := by
  haveI : Subsingleton ↥(Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  haveI : Subsingleton ↥(Spec (CommRingCat.of (DualNumber k))) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum (DualNumber k)))
  refine overSection_ext X ?_ he ?_
  · rw [Category.assoc, hg, specMap_fstRingHom_comp]
  · have h0 : (Spec.map (CommRingCat.ofHom
        (DualNumber.fstRingHom (R := k)))).base default
          = closedPoint (DualNumber k) := Subsingleton.elim _ _
    rw [Scheme.Hom.comp_apply, h0, hbase]

/-! ## §3. The fiber and kernel descriptions of the tangent space -/

/-- **The tangent space of a represented functor, as a fiber.** Let `F` be a
functor on `Over (Spec k)` represented by a `k`-scheme `X`, and `e` a section
of the structure morphism. Composition with the representing natural
bijection identifies the pointed dual-number points of `X` at `e` — the
Zariski tangent space `T_e X` in functor-of-points form — with the fiber of
the restriction map `F(Spec k[ε]) → F(Spec k)` (along the `ε ↦ 0` point) over
the class of `e`. The base-point condition transports to the fiber condition
by `specMap_fstRingHom_comp_eq` (sections through a common rational point
coincide). -/
noncomputable def pointedDualNumberPointsEquivRepresentableFiber
    (X : Over (Spec (CommRingCat.of k)))
    {F : (Over (Spec (CommRingCat.of k)))ᵒᵖ ⥤ Type v}
    (rep : F.RepresentableBy X)
    {e : Spec (CommRingCat.of k) ⟶ X.left}
    (he : e ≫ X.hom = 𝟙 (Spec (CommRingCat.of k))) :
    {g : Spec (CommRingCat.of (DualNumber k)) ⟶ X.left //
        g ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))
          ∧ g.base (closedPoint (DualNumber k)) = e.base default}
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
        have hleft : Spec.map (CommRingCat.ofHom (DualNumber.fstRingHom (R := k)))
            ≫ (rep.homEquiv.symm a.1).left = e :=
          congrArg CategoryTheory.CommaMorphism.left hcomp
        calc (rep.homEquiv.symm a.1).left.base (closedPoint (DualNumber k))
            = (Spec.map (CommRingCat.ofHom (DualNumber.fstRingHom (R := k)))
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
    have h : ∀ (w : (rep.homEquiv.symm a.1).left ≫ X.hom = (overDualNumber k).hom),
        rep.homEquiv (Over.homMk (rep.homEquiv.symm a.1).left w) = a.1 := by
      intro w
      rw [show Over.homMk (rep.homEquiv.symm a.1).left w = rep.homEquiv.symm a.1 from
        Over.OverMorphism.ext rfl, Equiv.apply_symm_apply]
    exact h _)

/-- **The tangent space of a representably group-valued functor, as a
kernel** (Kleiman §5 Thm.~5.11, representability leg). Let `G` be an
`AddCommGrpCat`-valued functor on `Over (Spec k)` whose set-valued shadow is
represented by a `k`-scheme `X`, and `e` a section of the structure morphism.
Then the pointed dual-number points of `X` at `e` biject with the **kernel**
of the restriction homomorphism `G(Spec k[ε]) →+ G(Spec k)`: the fiber
description of `pointedDualNumberPointsEquivRepresentableFiber` is normalised
by translating with the constant tangent vector at `e` (the augmentation
composed with `e`, `AddMonoidHom.fiberEquivKer'`).

For `G = PicSharp.relPresheaf C` and `X = PicScheme C` this is
`T_e Pic_{C/k} ≃ ker(Pic^♯(Spec k[ε]) → Pic^♯(Spec k))`, consumed by
`Pic0.cotangentSpaceDual_equiv_relPicKernel`
(`Picard/Pic0AbelianVariety.lean`). -/
noncomputable def pointedDualNumberPointsEquivAddKernel
    (X : Over (Spec (CommRingCat.of k)))
    (G : (Over (Spec (CommRingCat.of k)))ᵒᵖ ⥤ AddCommGrpCat.{v})
    (rep : (G ⋙ CategoryTheory.forget AddCommGrpCat.{v}).RepresentableBy X)
    {e : Spec (CommRingCat.of k) ⟶ X.left}
    (he : e ≫ X.hom = 𝟙 (Spec (CommRingCat.of k))) :
    {g : Spec (CommRingCat.of (DualNumber k)) ⟶ X.left //
        g ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))
          ∧ g.base (closedPoint (DualNumber k)) = e.base default}
      ≃ {a : (G.obj (Opposite.op (overDualNumber k))) //
          (G.map (overDualNumberZero k).op).hom a = 0} := by
  -- the constant tangent vector at `e`, mapping to the class of `e`
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
      (AddMonoidHom.fiberEquivKer' (G.map (overDualNumberZero k).op).hom
        (rep.homEquiv (overDualNumberAugment k ≫
          (Over.homMk e he : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X))))

/-! ## §4. The Mumford `ε ↦ aε` scaling of the dual-number object

The `k`-module structure on the tangent space of a group functor (Mumford,
"Abelian varieties", §II.4; the Kleiman §5 Thm.~5.11 linearity bookkeeping)
scales a tangent vector `Spec k[ε] → X` by precomposition with the
`ε ↦ aε` endomorphism of `Spec k[ε]`. This section provides that
endomorphism in `Over (Spec k)` together with its interaction with the
retract pair: it fixes the `ε ↦ 0` point, composes multiplicatively, is the
identity at `a = 1`, and collapses to the constant retract at `a = 0`. -/

/-- The `ε ↦ aε` scaling commutes with the structure morphism of the
dual-number object: on rings, `scaleRingHom a ∘ inl = inl`
(`DualNumber.scaleRingHom_comp_algebraMap`). -/
lemma specMap_scaleRingHom_comp (a : k) :
    Spec.map (CommRingCat.ofHom (DualNumber.scaleRingHom a)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))
      = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) := by
  have h : CommRingCat.ofHom (algebraMap k (DualNumber k)) ≫
      CommRingCat.ofHom (DualNumber.scaleRingHom a)
        = CommRingCat.ofHom (algebraMap k (DualNumber k)) := by
    rw [← CommRingCat.ofHom_comp, DualNumber.scaleRingHom_comp_algebraMap]
  rw [← Spec.map_comp, h]

/-- **The `ε ↦ aε` scaling of the dual-number object**, as an endomorphism
of `Spec k[ε]` in `Over (Spec k)`. Precomposition with it is Mumford's
scalar multiplication by `a` on tangent vectors (functor-of-points Zariski
tangent space); pushing through a group-valued functor it becomes the scalar
action on the dual-number kernel (`relPicKernelSMul` below). -/
noncomputable def overDualNumberScale (a : k) :
    overDualNumber k ⟶ overDualNumber k :=
  Over.homMk (Spec.map (CommRingCat.ofHom (DualNumber.scaleRingHom a)))
    (specMap_scaleRingHom_comp a)

/-- The scaling fixes the `ε ↦ 0` point:
`overDualNumberZero ≫ overDualNumberScale a = overDualNumberZero`. This is
why the scaling preserves the kernel of the restriction map of a functor
along `ε ↦ 0`. -/
lemma overDualNumberZero_comp_scale (a : k) :
    overDualNumberZero k ≫ overDualNumberScale a = overDualNumberZero k := by
  have hr : CommRingCat.ofHom (DualNumber.scaleRingHom a) ≫
      CommRingCat.ofHom (DualNumber.fstRingHom (R := k))
        = CommRingCat.ofHom (DualNumber.fstRingHom (R := k)) := by
    rw [← CommRingCat.ofHom_comp, DualNumber.fstRingHom_comp_scaleRingHom]
  have h : Spec.map (CommRingCat.ofHom (DualNumber.fstRingHom (R := k))) ≫
      Spec.map (CommRingCat.ofHom (DualNumber.scaleRingHom a))
        = Spec.map (CommRingCat.ofHom (DualNumber.fstRingHom (R := k))) := by
    rw [← Spec.map_comp, hr]
  apply Over.OverMorphism.ext
  exact h

/-- The scaling composes multiplicatively:
`overDualNumberScale a ≫ overDualNumberScale b = overDualNumberScale (a * b)`
(note both orders agree, `k` being commutative). -/
lemma overDualNumberScale_comp (a b : k) :
    overDualNumberScale (k := k) a ≫ overDualNumberScale b
      = overDualNumberScale (a * b) := by
  have hr : CommRingCat.ofHom (DualNumber.scaleRingHom b) ≫
      CommRingCat.ofHom (DualNumber.scaleRingHom a)
        = CommRingCat.ofHom (DualNumber.scaleRingHom (a * b)) := by
    rw [← CommRingCat.ofHom_comp, DualNumber.scaleRingHom_comp_scaleRingHom]
  have h : Spec.map (CommRingCat.ofHom (DualNumber.scaleRingHom a)) ≫
      Spec.map (CommRingCat.ofHom (DualNumber.scaleRingHom b))
        = Spec.map (CommRingCat.ofHom (DualNumber.scaleRingHom (a * b))) := by
    rw [← Spec.map_comp, hr]
  apply Over.OverMorphism.ext
  exact h

/-- Scaling by `1` is the identity of the dual-number object. -/
lemma overDualNumberScale_one :
    overDualNumberScale (1 : k) = 𝟙 (overDualNumber k) := by
  have hr : CommRingCat.ofHom (DualNumber.scaleRingHom (1 : k))
      = 𝟙 (CommRingCat.of (DualNumber k)) := by
    rw [DualNumber.scaleRingHom_one]
    rfl
  have h : Spec.map (CommRingCat.ofHom (DualNumber.scaleRingHom (1 : k)))
      = 𝟙 (Spec (CommRingCat.of (DualNumber k))) := by
    rw [hr, Spec.map_id]
  apply Over.OverMorphism.ext
  exact h

/-- Scaling by `0` collapses to the constant retract: it factors as the
augmentation followed by the `ε ↦ 0` point. This is why `0 • v` is the zero
tangent vector. -/
lemma overDualNumberScale_zero :
    overDualNumberScale (0 : k)
      = overDualNumberAugment k ≫ overDualNumberZero k := by
  have hr : CommRingCat.ofHom (DualNumber.fstRingHom (R := k)) ≫
      CommRingCat.ofHom (algebraMap k (DualNumber k))
        = CommRingCat.ofHom (DualNumber.scaleRingHom (0 : k)) := by
    rw [← CommRingCat.ofHom_comp, DualNumber.scaleRingHom_zero]
  have h : Spec.map (CommRingCat.ofHom (DualNumber.scaleRingHom (0 : k)))
      = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫
          Spec.map (CommRingCat.ofHom (DualNumber.fstRingHom (R := k))) := by
    rw [← hr, Spec.map_comp]
  apply Over.OverMorphism.ext
  exact h

/-! ## §5. The scaling action on the dual-number kernel of a group functor -/

/-- **Mumford's tangent-vector scaling on the dual-number kernel.** For an
`AddCommGrpCat`-valued functor `G` on `Over (Spec k)`, functoriality along
the `ε ↦ aε` scaling preserves the kernel of the restriction homomorphism
`G(Spec k[ε]) →+ G(Spec k)` — the scaling fixes the `ε ↦ 0` point
(`overDualNumberZero_comp_scale`). This is the scalar multiplication of the
Kleiman/Mumford `k`-module structure on the tangent space of a group functor
at the identity (Mumford, "Abelian varieties", §II.4), transported to the
kernel model of `pointedDualNumberPointsEquivAddKernel`.

Additivity in the vector is `map_add` of `G.map (overDualNumberScale a).op`;
the multiplicative-monoid laws are `relPicKernelSMul_one` /
`relPicKernelSMul_mul` / `relPicKernelSMul_zero` below. Distributivity
`(a + b) • x = a • x + b • x` is **not** formal at this generality (it needs
the sheaf condition of `G` against `k[ε] ×_k k[ε] = k[ε₁, ε₂]`) and belongs
to the cocycle leg of Kleiman §5 Thm.~5.11. -/
noncomputable def relPicKernelSMul
    (G : (Over (Spec (CommRingCat.of k)))ᵒᵖ ⥤ AddCommGrpCat.{v}) (a : k)
    (x : {x : G.obj (Opposite.op (overDualNumber k)) //
      (G.map (overDualNumberZero k).op).hom x = 0}) :
    {x : G.obj (Opposite.op (overDualNumber k)) //
      (G.map (overDualNumberZero k).op).hom x = 0} :=
  ⟨(G.map (overDualNumberScale a).op).hom x.1, by
    have h : (G.map (overDualNumberZero k).op).hom
        ((G.map (overDualNumberScale a).op).hom x.1)
      = (G.map (overDualNumberZero k ≫ overDualNumberScale a).op).hom x.1 := by
      rw [op_comp, G.map_comp]
      rfl
    rw [h, overDualNumberZero_comp_scale, x.2]⟩

/-- `1 • x = x` for the Mumford scaling on the dual-number kernel. -/
lemma relPicKernelSMul_one
    (G : (Over (Spec (CommRingCat.of k)))ᵒᵖ ⥤ AddCommGrpCat.{v})
    (x : {x : G.obj (Opposite.op (overDualNumber k)) //
      (G.map (overDualNumberZero k).op).hom x = 0}) :
    relPicKernelSMul G 1 x = x := by
  apply Subtype.ext
  change (G.map (overDualNumberScale (1 : k)).op).hom x.1 = x.1
  rw [overDualNumberScale_one, op_id, G.map_id]
  rfl

/-- `a • (b • x) = (a * b) • x` for the Mumford scaling on the dual-number
kernel. -/
lemma relPicKernelSMul_mul
    (G : (Over (Spec (CommRingCat.of k)))ᵒᵖ ⥤ AddCommGrpCat.{v}) (a b : k)
    (x : {x : G.obj (Opposite.op (overDualNumber k)) //
      (G.map (overDualNumberZero k).op).hom x = 0}) :
    relPicKernelSMul G a (relPicKernelSMul G b x)
      = relPicKernelSMul G (a * b) x := by
  apply Subtype.ext
  have h : (G.map (overDualNumberScale a).op).hom
      ((G.map (overDualNumberScale b).op).hom x.1)
    = (G.map (overDualNumberScale a ≫ overDualNumberScale b).op).hom x.1 := by
    rw [op_comp, G.map_comp]
    rfl
  change (G.map (overDualNumberScale a).op).hom
      ((G.map (overDualNumberScale b).op).hom x.1)
    = (G.map (overDualNumberScale (a * b)).op).hom x.1
  rw [h, overDualNumberScale_comp]

/-- `0 • x = 0` for the Mumford scaling on the dual-number kernel: scaling
by `0` factors through the restriction to `Spec k`, which kills kernel
elements. -/
lemma relPicKernelSMul_zero
    (G : (Over (Spec (CommRingCat.of k)))ᵒᵖ ⥤ AddCommGrpCat.{v})
    (x : {x : G.obj (Opposite.op (overDualNumber k)) //
      (G.map (overDualNumberZero k).op).hom x = 0}) :
    (relPicKernelSMul G (0 : k) x).1 = 0 := by
  change (G.map (overDualNumberScale (0 : k)).op).hom x.1 = 0
  have h : (G.map (overDualNumberAugment k ≫ overDualNumberZero k).op).hom x.1
      = (G.map (overDualNumberAugment k).op).hom
          ((G.map (overDualNumberZero k).op).hom x.1) := by
    rw [op_comp, G.map_comp]
    rfl
  rw [overDualNumberScale_zero, h, x.2, map_zero]

end AlgebraicGeometry

/-! ## §6. The two-chart Čech unit-cocycle engine (Kleiman §5 Thm 5.11, algebra layer)

The pure-algebra heart of the cocycle leg. A *two-chart datum* is a pair of
ring homomorphisms `ρ₁ : A₁ →+* B`, `ρ₂ : A₂ →+* B` — think `Aᵢ = Γ(Uᵢ, 𝒪_C)`
the section rings of a 2-affine cover and `B = Γ(U₁ ⊓ U₂, 𝒪_C)` the overlap
ring, with `ρᵢ` the restrictions. The two-cover Čech `Ȟ¹` of *units* is the
quotient `Bˣ ⧸ (im ρ₁ˣ · im ρ₂ˣ)` of transition units by coboundaries — the
Picard group of the cover in Čech form. Applying the same construction to the
dual-number thickening (`Aᵢ[ε] →+* B[ε]` via `DualNumber.mapRingHom`) and
reducing mod `ε` (`unitsFst`, which maps coboundaries to coboundaries) gives
the restriction map `Ȟ¹ˣ(B[ε]) →* Ȟ¹ˣ(B)` of `Pic(C_ε) → Pic(C)`.

The engine computes the **kernel** of that reduction: the truncated
exponential `b ↦ [1 + b ε]` induces an additive equivalence

```
B ⧸ (ρ₁(A₁) + ρ₂(A₂))  ≃+  ker(Ȟ¹ˣ(B[ε]) → Ȟ¹ˣ(B))
```

(`truncExpCechKernelAddEquiv`), whose source is exactly the two-chart Čech
cokernel shape of `AffineCoverMVSquare.H1Cok` (`Γ(U₁ ⊓ U₂) ⧸ range
sectionDiff`) — i.e. `H¹(C, 𝒪_C)` on a curve. Equivariance for the Mumford
`ε ↦ tε` scaling (`scaleRingHom`) is provided pointwise:
`unitsScale_mk_truncExpUnit` shows the scaling acts on truncated-exponential
classes as `b ↦ t·b`, matching the `k`-scalar action on `H1Cok`.

Everything here is elementary commutative algebra: no schemes, no sheaves.
The remaining geometric distance to `Pic0.finrank_cotangentSpaceDual_eq_finrank_h1Cok`
(`Picard/Pic0AbelianVariety.lean`) is the chart-triviality/section-identification
substrate (`Γ(V × Spec k[ε], 𝒪) ≅ Γ(V, 𝒪)[ε]` for affine `V`, and triviality on
charts of invertible sheaves on the thickening restricting trivially mod `ε`),
which identifies the relative-Pic kernel with the kernel computed here. -/

namespace DualNumber

open TrivSqZeroExt

section UnitHelpers

variable {R : Type w} [CommRing R]

/-- `mapRingHom` intertwines the constant inclusions: `mapRingHom ρ (inl a) =
inl (ρ a)`. -/
theorem mapRingHom_inl {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (ρ : A →+* B) (a : A) :
    mapRingHom ρ (inl a : A[ε]) = (inl (ρ a) : B[ε]) :=
  TrivSqZeroExt.ext (by simp) (by simp)

/-- `mapRingHom` intertwines the unit-level constant inclusions `unitsInl`. -/
theorem unitsMap_mapRingHom_unitsInl {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (ρ : A →+* B) (v : Aˣ) :
    Units.map (mapRingHom ρ).toMonoidHom (unitsInl v)
      = unitsInl (Units.map ρ.toMonoidHom v) :=
  Units.ext (by simpa using mapRingHom_inl ρ (v : A))

/-- Reduction mod `ε` on units retracts the constant inclusion:
`unitsFst (unitsInl a) = a`. -/
@[simp]
theorem unitsFst_unitsInl (a : Rˣ) : unitsFst (unitsInl a) = a :=
  Units.ext (by simp)

/-- Truncated-exponential units reduce to `1` mod `ε`. -/
@[simp]
theorem unitsFst_truncExpUnit (b : R) : unitsFst (truncExpUnit b) = 1 :=
  Units.ext (by simp)

/-- The truncated exponential at `0` is the unit `1`. -/
@[simp]
theorem truncExpUnit_zero : truncExpUnit (0 : R) = 1 :=
  Units.ext (by simp)

/-- **The unit decomposition of the dual numbers, equational form**: every
unit of `R[ε]` is the constant inclusion of its reduction times a truncated
exponential — `u = inl(u₀) · (1 + c ε)` with `u₀ = unitsFst u` and
`c = fst(u⁻¹) · snd(u)`. Pointwise restatement of `unitsEquivProd.left_inv`. -/
theorem unitsInl_unitsFst_mul_truncExpUnit (u : (R[ε])ˣ) :
    unitsInl (unitsFst u)
        * truncExpUnit (((u⁻¹ : (R[ε])ˣ) : R[ε]).fst * ((u : (R[ε])ˣ) : R[ε]).snd)
      = u := by
  have h := unitsEquivProd.symm_apply_apply u
  rw [unitsEquivProd_symm_apply] at h
  exact h

/-- The truncated exponential is injective in the equational (unit) form. -/
theorem truncExpUnit_injective : Function.Injective (truncExpUnit (R := R)) := by
  intro b c h
  have := congrArg (fun u : (R[ε])ˣ => ((u : (R[ε])ˣ) : R[ε]).snd) h
  simpa using this

/-- The Mumford `ε ↦ aε` scaling acts on truncated-exponential units by
scaling the infinitesimal: `(1 + b ε) ↦ (1 + (a b) ε)`. -/
theorem unitsScale_truncExpUnit (a b : R) :
    Units.map (scaleRingHom a).toMonoidHom (truncExpUnit b) = truncExpUnit (a * b) :=
  Units.ext (TrivSqZeroExt.ext (by simp) (by simp))

/-- The Mumford scaling is compatible with the functorial map of dual-number
rings: `mapRingHom ρ ∘ scaleRingHom s = scaleRingHom (ρ s) ∘ mapRingHom ρ`. -/
theorem mapRingHom_comp_scaleRingHom {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (ρ : A →+* B) (s : A) :
    (mapRingHom ρ).comp (scaleRingHom s) = (scaleRingHom (ρ s)).comp (mapRingHom ρ) :=
  RingHom.ext fun x => TrivSqZeroExt.ext (by simp) (by simp)

end UnitHelpers

section CechEngine

variable {A₁ : Type u} {A₂ : Type v} {B : Type w}
variable [CommRing A₁] [CommRing A₂] [CommRing B]

/-- **The Čech coboundary subgroup of a two-chart datum**: for restriction
homomorphisms `ρ₁ : A₁ →+* B`, `ρ₂ : A₂ →+* B` onto the overlap ring `B`, the
subgroup `im(ρ₁ˣ) · im(ρ₂ˣ) ≤ Bˣ` of transition units that are coboundaries
of the 2-cover. The quotient `Bˣ ⧸ cechCoboundaryUnits ρ₁ ρ₂` is the
two-cover Čech `Ȟ¹` of units — the Čech-cocycle Picard group of the cover. -/
def cechCoboundaryUnits (ρ₁ : A₁ →+* B) (ρ₂ : A₂ →+* B) : Subgroup Bˣ :=
  (Units.map ρ₁.toMonoidHom).range ⊔ (Units.map ρ₂.toMonoidHom).range

/-- Membership in the Čech coboundary subgroup: `u` is a coboundary iff
`u = ρ₁ˣ(v₁) · ρ₂ˣ(v₂)` for chart units `vᵢ ∈ Aᵢˣ` (the sign convention with
a product rather than a quotient is immaterial: the ranges are subgroups). -/
theorem mem_cechCoboundaryUnits {ρ₁ : A₁ →+* B} {ρ₂ : A₂ →+* B} {u : Bˣ} :
    u ∈ cechCoboundaryUnits ρ₁ ρ₂
      ↔ ∃ (v₁ : A₁ˣ) (v₂ : A₂ˣ),
          Units.map ρ₁.toMonoidHom v₁ * Units.map ρ₂.toMonoidHom v₂ = u := by
  constructor
  · intro h
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp h
    obtain ⟨v₁, rfl⟩ := MonoidHom.mem_range.mp hy
    obtain ⟨v₂, rfl⟩ := MonoidHom.mem_range.mp hz
    exact ⟨v₁, v₂, rfl⟩
  · rintro ⟨v₁, v₂, rfl⟩
    exact Subgroup.mem_sup.mpr
      ⟨_, MonoidHom.mem_range.mpr ⟨v₁, rfl⟩, _, MonoidHom.mem_range.mpr ⟨v₂, rfl⟩, rfl⟩

/-- Chart units from the first chart are coboundaries. -/
theorem unitsMap_mem_cechCoboundaryUnits_left (ρ₁ : A₁ →+* B) (ρ₂ : A₂ →+* B)
    (v : A₁ˣ) : Units.map ρ₁.toMonoidHom v ∈ cechCoboundaryUnits ρ₁ ρ₂ :=
  mem_cechCoboundaryUnits.mpr ⟨v, 1, by simp⟩

/-- Chart units from the second chart are coboundaries. -/
theorem unitsMap_mem_cechCoboundaryUnits_right (ρ₁ : A₁ →+* B) (ρ₂ : A₂ →+* B)
    (v : A₂ˣ) : Units.map ρ₂.toMonoidHom v ∈ cechCoboundaryUnits ρ₁ ρ₂ :=
  mem_cechCoboundaryUnits.mpr ⟨1, v, by simp⟩

/-- **The additive Čech coboundary subgroup of a two-chart datum**:
`ρ₁(A₁) + ρ₂(A₂) ≤ B` as an additive subgroup. The quotient
`B ⧸ cechCoboundaryAdd ρ₁ ρ₂` is the two-cover Čech cokernel — for the
section rings of a 2-affine cover, exactly the carrier shape of
`AffineCoverMVSquare.H1Cok` (`Γ(U₁ ⊓ U₂) ⧸ range sectionDiff`; a difference
`ρ₁ a₁ - ρ₂ a₂` and a sum `ρ₁ a₁ + ρ₂ a₂` span the same subgroup). -/
def cechCoboundaryAdd (ρ₁ : A₁ →+* B) (ρ₂ : A₂ →+* B) : AddSubgroup B :=
  ρ₁.toAddMonoidHom.range ⊔ ρ₂.toAddMonoidHom.range

/-- Membership in the additive Čech coboundary subgroup. -/
theorem mem_cechCoboundaryAdd {ρ₁ : A₁ →+* B} {ρ₂ : A₂ →+* B} {b : B} :
    b ∈ cechCoboundaryAdd ρ₁ ρ₂ ↔ ∃ (a₁ : A₁) (a₂ : A₂), ρ₁ a₁ + ρ₂ a₂ = b := by
  constructor
  · intro h
    obtain ⟨y, hy, z, hz, rfl⟩ := AddSubgroup.mem_sup.mp h
    obtain ⟨a₁, rfl⟩ := AddMonoidHom.mem_range.mp hy
    obtain ⟨a₂, rfl⟩ := AddMonoidHom.mem_range.mp hz
    exact ⟨a₁, a₂, rfl⟩
  · rintro ⟨a₁, a₂, rfl⟩
    exact AddSubgroup.mem_sup.mpr
      ⟨_, AddMonoidHom.mem_range.mpr ⟨a₁, rfl⟩, _, AddMonoidHom.mem_range.mpr ⟨a₂, rfl⟩, rfl⟩

/-- Differences of chart sections are additive Čech coboundaries — the
subtraction form of membership, matching the difference-of-restrictions map
`AffineCoverMVSquare.sectionDiff` of the geometric consumer. Clean-binder
helper: state and use this on abstract rings, then transport the result along
the (defeq) carrier identifications of the sheaf dialect. -/
theorem sub_mem_cechCoboundaryAdd (ρ₁ : A₁ →+* B) (ρ₂ : A₂ →+* B)
    (a₁ : A₁) (a₂ : A₂) :
    ρ₁ a₁ - ρ₂ a₂ ∈ cechCoboundaryAdd ρ₁ ρ₂ :=
  mem_cechCoboundaryAdd.mpr ⟨a₁, -a₂, by rw [map_neg, ← sub_eq_add_neg]⟩

/-- Additive Čech coboundaries are differences of chart sections — the
subtraction form of the membership characterisation (converse of
`sub_mem_cechCoboundaryAdd`). -/
theorem exists_sub_of_mem_cechCoboundaryAdd {ρ₁ : A₁ →+* B} {ρ₂ : A₂ →+* B}
    {b : B} (h : b ∈ cechCoboundaryAdd ρ₁ ρ₂) :
    ∃ (a₁ : A₁) (a₂ : A₂), ρ₁ a₁ - ρ₂ a₂ = b := by
  obtain ⟨a₁, a₂, ha⟩ := mem_cechCoboundaryAdd.mp h
  exact ⟨a₁, -a₂, by rw [map_neg, sub_neg_eq_add, ha]⟩

/-- **The truncated exponential detects the additive coboundaries** (the
well-definedness/injectivity heart of the Kleiman §5 Thm 5.11 cocycle leg):
the unit `1 + b ε` on the dual-number overlap ring is a coboundary of the
thickened cover iff `b` is an additive coboundary `ρ₁(a₁) + ρ₂(a₂)`.

Forward direction: decompose the two chart units `wᵢ ∈ (Aᵢ[ε])ˣ` as
`inl(wᵢ₀)·(1 + cᵢ ε)` (`unitsInl_unitsFst_mul_truncExpUnit`); reducing the
coboundary relation mod `ε` forces the constant parts to cancel, leaving
`1 + b ε = 1 + (ρ₁ c₁ + ρ₂ c₂) ε`. -/
theorem truncExpUnit_mem_cechCoboundaryUnits_iff
    (ρ₁ : A₁ →+* B) (ρ₂ : A₂ →+* B) (b : B) :
    truncExpUnit b ∈ cechCoboundaryUnits (mapRingHom ρ₁) (mapRingHom ρ₂)
      ↔ b ∈ cechCoboundaryAdd ρ₁ ρ₂ := by
  constructor
  · intro h
    obtain ⟨w₁, w₂, hw⟩ := mem_cechCoboundaryUnits.mp h
    rw [← unitsInl_unitsFst_mul_truncExpUnit w₁,
      ← unitsInl_unitsFst_mul_truncExpUnit w₂, map_mul, map_mul,
      unitsMap_mapRingHom_unitsInl, unitsMap_mapRingHom_unitsInl,
      map_mapRingHom_truncExpUnit, map_mapRingHom_truncExpUnit,
      mul_mul_mul_comm, ← map_mul, ← truncExpUnit_add] at hw
    -- reduce mod `ε`: the constant part of the coboundary is trivial
    have hfst := congrArg unitsFst hw
    rw [map_mul, unitsFst_unitsInl, unitsFst_truncExpUnit, mul_one,
      unitsFst_truncExpUnit] at hfst
    rw [hfst, map_one, one_mul] at hw
    exact mem_cechCoboundaryAdd.mpr ⟨_, _, truncExpUnit_injective hw⟩
  · intro h
    obtain ⟨a₁, a₂, rfl⟩ := mem_cechCoboundaryAdd.mp h
    refine mem_cechCoboundaryUnits.mpr ⟨truncExpUnit a₁, truncExpUnit a₂, ?_⟩
    rw [map_mapRingHom_truncExpUnit, map_mapRingHom_truncExpUnit, ← truncExpUnit_add]

/-- Reduction mod `ε` on units carries thickened coboundaries to
coboundaries (`unitsFst` naturality), so it descends to the Čech `Ȟ¹`
quotients. -/
theorem cechCoboundaryUnits_le_comap_unitsFst (ρ₁ : A₁ →+* B) (ρ₂ : A₂ →+* B) :
    cechCoboundaryUnits (mapRingHom ρ₁) (mapRingHom ρ₂) ≤
      (cechCoboundaryUnits ρ₁ ρ₂).comap (unitsFst (R := B)) := by
  intro u hu
  obtain ⟨w₁, w₂, rfl⟩ := mem_cechCoboundaryUnits.mp hu
  refine Subgroup.mem_comap.mpr (mem_cechCoboundaryUnits.mpr
    ⟨unitsFst w₁, unitsFst w₂, ?_⟩)
  rw [map_mul, unitsFst_map_mapRingHom, unitsFst_map_mapRingHom]

/-- **The reduction map of two-chart Čech `Ȟ¹`-of-units groups**
`Ȟ¹ˣ(B[ε]) →* Ȟ¹ˣ(B)` induced by reduction mod `ε` — the Čech-cocycle
incarnation of the restriction `Pic(C ×_k Spec k[ε]) → Pic(C)` along
`ε ↦ 0`. Its kernel is computed by `truncExpCechKernelAddEquiv` below. -/
noncomputable def cechUnitsReduction (ρ₁ : A₁ →+* B) (ρ₂ : A₂ →+* B) :
    ((B[ε])ˣ ⧸ cechCoboundaryUnits (mapRingHom ρ₁) (mapRingHom ρ₂)) →*
      Bˣ ⧸ cechCoboundaryUnits ρ₁ ρ₂ :=
  QuotientGroup.map _ _ (unitsFst (R := B))
    (cechCoboundaryUnits_le_comap_unitsFst ρ₁ ρ₂)

/-- Truncated-exponential classes lie in the kernel of the Čech reduction
map: `1 + b ε` reduces to `1` mod `ε`. -/
theorem cechUnitsReduction_mk_truncExpUnit (ρ₁ : A₁ →+* B) (ρ₂ : A₂ →+* B)
    (b : B) :
    cechUnitsReduction ρ₁ ρ₂ (QuotientGroup.mk (truncExpUnit b)) = 1 := by
  rw [cechUnitsReduction, QuotientGroup.map_mk, unitsFst_truncExpUnit,
    QuotientGroup.mk_one]

/-- Vanishing of a truncated-exponential class in the thickened Čech `Ȟ¹`:
`[1 + b ε] = 1` iff `b` is an additive coboundary. -/
theorem mk_truncExpUnit_eq_one_iff (ρ₁ : A₁ →+* B) (ρ₂ : A₂ →+* B) (b : B) :
    (QuotientGroup.mk (truncExpUnit b) :
        (B[ε])ˣ ⧸ cechCoboundaryUnits (mapRingHom ρ₁) (mapRingHom ρ₂)) = 1
      ↔ b ∈ cechCoboundaryAdd ρ₁ ρ₂ := by
  rw [QuotientGroup.eq_one_iff]
  exact truncExpUnit_mem_cechCoboundaryUnits_iff ρ₁ ρ₂ b

/-- **Every kernel class of the Čech reduction is a truncated exponential**
(the surjectivity heart of the Kleiman §5 Thm 5.11 cocycle leg): a class of
`Ȟ¹ˣ(B[ε])` restricting trivially mod `ε` is represented by `1 + b ε` for
some `b : B`. Proof: normalise a representative `u` by the (lifted) chart
units trivialising its reduction; the corrected unit has trivial constant
part, hence lies in the range of the truncated exponential
(`truncExp_range_eq_ker_unitsFst`). -/
theorem exists_mk_truncExpUnit_of_cechUnitsReduction_eq_one
    (ρ₁ : A₁ →+* B) (ρ₂ : A₂ →+* B)
    (x : (B[ε])ˣ ⧸ cechCoboundaryUnits (mapRingHom ρ₁) (mapRingHom ρ₂))
    (hx : cechUnitsReduction ρ₁ ρ₂ x = 1) :
    ∃ b : B, (QuotientGroup.mk (truncExpUnit b) :
      (B[ε])ˣ ⧸ cechCoboundaryUnits (mapRingHom ρ₁) (mapRingHom ρ₂)) = x := by
  revert hx
  induction x using QuotientGroup.induction_on with
  | H u =>
    intro hu
    rw [cechUnitsReduction, QuotientGroup.map_mk, QuotientGroup.eq_one_iff] at hu
    obtain ⟨v₁, v₂, hv⟩ := mem_cechCoboundaryUnits.mp hu
    -- the chart-unit correction of `u`
    have hker : unitsFst
        ((Units.map (mapRingHom ρ₁).toMonoidHom (unitsInl v₁))⁻¹ * u *
          (Units.map (mapRingHom ρ₂).toMonoidHom (unitsInl v₂))⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, map_inv, unitsMap_mapRingHom_unitsInl,
        unitsMap_mapRingHom_unitsInl, unitsFst_unitsInl, unitsFst_unitsInl, ← hv]
      group
    have hmem : (Units.map (mapRingHom ρ₁).toMonoidHom (unitsInl v₁))⁻¹ * u *
        (Units.map (mapRingHom ρ₂).toMonoidHom (unitsInl v₂))⁻¹
          ∈ (truncExp (R := B)).range := by
      rw [truncExp_range_eq_ker_unitsFst]
      exact MonoidHom.mem_ker.mpr hker
    obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp hmem
    refine ⟨m.toAdd, ?_⟩
    rw [← truncExp_apply, hm, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv, QuotientGroup.mk_inv,
      (QuotientGroup.eq_one_iff _).mpr
        (unitsMap_mem_cechCoboundaryUnits_left (mapRingHom ρ₁) (mapRingHom ρ₂)
          (unitsInl v₁)),
      (QuotientGroup.eq_one_iff _).mpr
        (unitsMap_mem_cechCoboundaryUnits_right (mapRingHom ρ₁) (mapRingHom ρ₂)
          (unitsInl v₂))]
    simp

/-- The truncated exponential as a monoid homomorphism into the kernel of
the Čech reduction map (multiplicative source `Multiplicative B`). -/
noncomputable def truncExpCechKernelMonoidHom (ρ₁ : A₁ →+* B) (ρ₂ : A₂ →+* B) :
    Multiplicative B →* (cechUnitsReduction ρ₁ ρ₂).ker where
  toFun b :=
    ⟨QuotientGroup.mk (truncExpUnit b.toAdd),
      MonoidHom.mem_ker.mpr (cechUnitsReduction_mk_truncExpUnit ρ₁ ρ₂ b.toAdd)⟩
  map_one' := Subtype.ext <| by
    change (QuotientGroup.mk (truncExpUnit ((1 : Multiplicative B).toAdd)) : _) = 1
    rw [toAdd_one, truncExpUnit_zero, QuotientGroup.mk_one]
  map_mul' b c := Subtype.ext <| by
    change (QuotientGroup.mk (truncExpUnit ((b * c).toAdd)) : _) = _
    rw [toAdd_mul, truncExpUnit_add, QuotientGroup.mk_mul]
    rfl

/-- **The truncated-exponential kernel computation** (Kleiman §5 Thm 5.11,
cocycle leg, algebra layer): for a two-chart datum `ρ₁ : A₁ →+* B`,
`ρ₂ : A₂ →+* B`, the truncated exponential `b ↦ [1 + b ε]` induces an
additive equivalence

```
B ⧸ (ρ₁(A₁) + ρ₂(A₂))  ≃+  ker( Ȟ¹ˣ(B[ε]) →* Ȟ¹ˣ(B) )
```

from the two-cover Čech cokernel (the `AffineCoverMVSquare.H1Cok` carrier
shape — `H¹(C, 𝒪_C)` for the section rings of a 2-affine cover of a curve)
onto the kernel of the dual-number Čech-units reduction (the two-chart
`ker(Pic(C_ε) → Pic(C))`). Well-definedness and injectivity are
`mk_truncExpUnit_eq_one_iff`; surjectivity is
`exists_mk_truncExpUnit_of_cechUnitsReduction_eq_one`; additivity is the
truncated-exponential functional equation `truncExpUnit_add`. -/
noncomputable def truncExpCechKernelAddEquiv (ρ₁ : A₁ →+* B) (ρ₂ : A₂ →+* B) :
    B ⧸ cechCoboundaryAdd ρ₁ ρ₂ ≃+
      Additive (cechUnitsReduction ρ₁ ρ₂).ker := by
  refine AddEquiv.ofBijective
    (QuotientAddGroup.lift (cechCoboundaryAdd ρ₁ ρ₂)
      (MonoidHom.toAdditiveRight (truncExpCechKernelMonoidHom ρ₁ ρ₂)) ?_) ⟨?_, ?_⟩
  · intro b hb
    apply Additive.toMul.injective
    apply Subtype.ext
    change (QuotientGroup.mk (truncExpUnit b) : _) = 1
    exact (mk_truncExpUnit_eq_one_iff ρ₁ ρ₂ b).mpr hb
  · rw [injective_iff_map_eq_zero]
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H b =>
      intro hbx
      have hb : (QuotientGroup.mk (truncExpUnit b) :
          (B[ε])ˣ ⧸ cechCoboundaryUnits (mapRingHom ρ₁) (mapRingHom ρ₂)) = 1 :=
        congrArg (fun y => (Additive.toMul y : (cechUnitsReduction ρ₁ ρ₂).ker).1) hbx
      rw [QuotientAddGroup.eq_zero_iff]
      exact (mk_truncExpUnit_eq_one_iff ρ₁ ρ₂ b).mp hb
  · intro y
    obtain ⟨b, hb⟩ := exists_mk_truncExpUnit_of_cechUnitsReduction_eq_one ρ₁ ρ₂
      (Additive.toMul y : (cechUnitsReduction ρ₁ ρ₂).ker).1
      (Additive.toMul y : (cechUnitsReduction ρ₁ ρ₂).ker).2
    exact ⟨QuotientAddGroup.mk b,
      Additive.toMul.injective (Subtype.ext hb)⟩

/-- Elementwise formula for the truncated-exponential kernel equivalence on
residue classes: `[b] ↦ [1 + b ε]`. Definitional. -/
theorem truncExpCechKernelAddEquiv_apply_mk (ρ₁ : A₁ →+* B) (ρ₂ : A₂ →+* B)
    (b : B) :
    ((Additive.toMul (truncExpCechKernelAddEquiv ρ₁ ρ₂ (QuotientAddGroup.mk b)) :
        (cechUnitsReduction ρ₁ ρ₂).ker) : _)
      = (QuotientGroup.mk (truncExpUnit b) :
          (B[ε])ˣ ⧸ cechCoboundaryUnits (mapRingHom ρ₁) (mapRingHom ρ₂)) :=
  rfl

/-! ### Mumford-scaling equivariance of the engine

The `ε ↦ tε` scaling of the overlap ring `B[ε]` (`scaleRingHom t`) preserves
the thickened coboundaries whenever the scalar is compatible with the charts
(`ρ₁ s₁ = t = ρ₂ s₂` — for a `k`-algebra datum, `sᵢ` and `t` are the images
of a common `a ∈ k`), hence descends to `Ȟ¹ˣ(B[ε])`, and it acts on
truncated-exponential classes exactly by `b ↦ t·b` — matching the `k`-scalar
action on the Čech cokernel side of `truncExpCechKernelAddEquiv`. -/

/-- The `ε ↦ tε` scaling preserves the thickened Čech coboundaries when the
scalar `t` is compatible with the charts (`ρ₁ s₁ = t = ρ₂ s₂`). -/
theorem cechCoboundaryUnits_le_comap_unitsScale (ρ₁ : A₁ →+* B) (ρ₂ : A₂ →+* B)
    {s₁ : A₁} {s₂ : A₂} {t : B} (h₁ : ρ₁ s₁ = t) (h₂ : ρ₂ s₂ = t) :
    cechCoboundaryUnits (mapRingHom ρ₁) (mapRingHom ρ₂) ≤
      (cechCoboundaryUnits (mapRingHom ρ₁) (mapRingHom ρ₂)).comap
        (Units.map (scaleRingHom t).toMonoidHom) := by
  intro u hu
  obtain ⟨w₁, w₂, rfl⟩ := mem_cechCoboundaryUnits.mp hu
  refine Subgroup.mem_comap.mpr (mem_cechCoboundaryUnits.mpr
    ⟨Units.map (scaleRingHom s₁).toMonoidHom w₁,
     Units.map (scaleRingHom s₂).toMonoidHom w₂, ?_⟩)
  rw [map_mul]
  congr 1
  · apply Units.ext
    simp only [Units.coe_map]
    exact (RingHom.congr_fun (mapRingHom_comp_scaleRingHom ρ₁ s₁) (w₁ : A₁[ε])).trans
      (by rw [h₁]; rfl)
  · apply Units.ext
    simp only [Units.coe_map]
    exact (RingHom.congr_fun (mapRingHom_comp_scaleRingHom ρ₂ s₂) (w₂ : A₂[ε])).trans
      (by rw [h₂]; rfl)

/-- **Equivariance of the truncated-exponential classes under the Mumford
scaling**: the `ε ↦ tε` scaling of `Ȟ¹ˣ(B[ε])` carries `[1 + b ε]` to
`[1 + (t·b) ε]` — through `truncExpCechKernelAddEquiv`, the scaling acts on
the Čech cokernel `B ⧸ (ρ₁(A₁) + ρ₂(A₂))` as multiplication by `t`, i.e. as
the `k`-scalar action for a `k`-algebra two-chart datum. -/
theorem unitsScale_mk_truncExpUnit (ρ₁ : A₁ →+* B) (ρ₂ : A₂ →+* B)
    {s₁ : A₁} {s₂ : A₂} {t : B} (h₁ : ρ₁ s₁ = t) (h₂ : ρ₂ s₂ = t) (b : B) :
    QuotientGroup.map _ _ (Units.map (scaleRingHom t).toMonoidHom)
        (cechCoboundaryUnits_le_comap_unitsScale ρ₁ ρ₂ h₁ h₂)
        (QuotientGroup.mk (truncExpUnit b))
      = (QuotientGroup.mk (truncExpUnit (t * b)) :
          (B[ε])ˣ ⧸ cechCoboundaryUnits (mapRingHom ρ₁) (mapRingHom ρ₂)) := by
  rw [QuotientGroup.map_mk, unitsScale_truncExpUnit]

end CechEngine

/-! ## §7. Dual numbers under base change: `A ⊗[k] k[ε] ≃ₐ[A] A[ε]`

The algebra core of the chart-sections identification (substrate piece (i) of
the geometric cocycle leg): for an affine chart `V = Spec A` of the curve, the
base-changed chart `V ×_{Spec k} Spec k[ε]` is `Spec (A ⊗[k] k[ε])`
(Mathlib's `pullbackSpecIso`), and this section supplies the missing ring
identification `A ⊗[k] k[ε] ≃ₐ[A] A[ε]` — so the thickened chart sections are
the dual numbers of the chart ring, which is what feeds the two-chart
unit-cocycle engine of §6 (`Γ((U₁ ⊓ U₂)_ε) = Γ(U₁ ⊓ U₂)[ε]`, transition units
in `(B[ε])ˣ`). The trivial-square-zero base is finite free, so no flatness
input is needed: the inverse is written down explicitly
(`x ↦ x.fst ⊗ 1 + x.snd ⊗ ε`). -/

section BaseChange

open TensorProduct

variable (k : Type u) (A : Type v) [CommRing k] [CommRing A] [Algebra k A]

/-- The functorial dual-number map `k[ε] → A[ε]` over the algebra map
`k → A`, as a `k`-algebra homomorphism (`mapRingHom` with its
`algebraMap`-compatibility, which holds componentwise). -/
def mapAlgHom : DualNumber k →ₐ[k] DualNumber A :=
  { mapRingHom (algebraMap k A) with
    commutes' := fun c => by
      refine TrivSqZeroExt.ext ?_ ?_ <;>
        simp [TrivSqZeroExt.algebraMap_eq_inl' k A, TrivSqZeroExt.algebraMap_eq_inl] }

@[simp]
theorem mapAlgHom_apply (x : DualNumber k) :
    mapAlgHom k A x = mapRingHom (algebraMap k A) x := rfl

/-- The base-change comparison `A ⊗[k] k[ε] →ₐ[A] A[ε]`, `a ⊗ y ↦ a · ȳ`
(the `A`-algebra map extending `mapAlgHom` along scalar extension,
`AlgHom.liftEquiv`). An isomorphism by `baseChangeAlgHom_bijective`. -/
noncomputable def baseChangeAlgHom : A ⊗[k] DualNumber k →ₐ[A] DualNumber A :=
  AlgHom.liftEquiv k A (DualNumber k) (DualNumber A) (mapAlgHom k A)

@[simp]
theorem baseChangeAlgHom_tmul (a : A) (y : DualNumber k) :
    baseChangeAlgHom k A (a ⊗ₜ[k] y) = a • mapRingHom (algebraMap k A) y := by
  simp [baseChangeAlgHom, AlgHom.liftEquiv]

/-- The base-change comparison is bijective: the two-sided inverse is the
explicit `x ↦ x.fst ⊗ 1 + x.snd ⊗ ε` (the dual numbers are finite free over
the base, so no flatness is needed). -/
theorem baseChangeAlgHom_bijective : Function.Bijective (baseChangeAlgHom k A) := by
  have hGF : Function.LeftInverse
      (fun x : DualNumber A =>
        x.fst ⊗ₜ[k] (1 : DualNumber k) + x.snd ⊗ₜ[k] (ε : DualNumber k))
      (baseChangeAlgHom k A) := by
    intro z
    dsimp only
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a y =>
        rw [baseChangeAlgHom_tmul]
        have hfst : (a • mapRingHom (algebraMap k A) y).fst = y.fst • a := by
          rw [TrivSqZeroExt.fst_smul, smul_eq_mul, fst_mapRingHom, Algebra.smul_def,
            mul_comm]
        have hsnd : (a • mapRingHom (algebraMap k A) y).snd = y.snd • a := by
          rw [TrivSqZeroExt.snd_smul, smul_eq_mul, snd_mapRingHom, Algebra.smul_def,
            mul_comm]
        rw [hfst, hsnd, smul_tmul, smul_tmul, ← TensorProduct.tmul_add]
        congr 1
        refine TrivSqZeroExt.ext ?_ ?_ <;> simp
    | add z₁ z₂ ih₁ ih₂ =>
        rw [map_add, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add,
          TensorProduct.add_tmul, TensorProduct.add_tmul, add_add_add_comm, ih₁, ih₂]
  have hFG : Function.RightInverse
      (fun x : DualNumber A =>
        x.fst ⊗ₜ[k] (1 : DualNumber k) + x.snd ⊗ₜ[k] (ε : DualNumber k))
      (baseChangeAlgHom k A) := by
    intro x
    dsimp only
    rw [map_add, baseChangeAlgHom_tmul, baseChangeAlgHom_tmul]
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp [smul_eq_mul]
  exact ⟨hGF.injective, hFG.surjective⟩

/-- **Dual numbers under base change** (substrate piece (i), algebra core):
for a `k`-algebra `A`, extension of scalars of the dual numbers is the dual
numbers of `A` — `A ⊗[k] k[ε] ≃ₐ[A] A[ε]`, `a ⊗ y ↦ a · ȳ`. Composed with
Mathlib's `pullbackSpecIso`, this identifies the sections of a base-changed
affine chart `V × Spec k[ε]` with `Γ(V, 𝒪)[ε]` — the section rings the
two-chart unit-cocycle engine of §6 consumes. -/
noncomputable def baseChangeAlgEquiv : A ⊗[k] DualNumber k ≃ₐ[A] DualNumber A :=
  AlgEquiv.ofBijective (baseChangeAlgHom k A) (baseChangeAlgHom_bijective k A)

@[simp]
theorem baseChangeAlgEquiv_tmul (a : A) (y : DualNumber k) :
    baseChangeAlgEquiv k A (a ⊗ₜ[k] y) = a • mapRingHom (algebraMap k A) y :=
  baseChangeAlgHom_tmul k A a y

/-- The inverse of the base-change comparison, explicitly:
`x ↦ x.fst ⊗ 1 + x.snd ⊗ ε`. -/
theorem baseChangeAlgEquiv_symm_apply (x : DualNumber A) :
    (baseChangeAlgEquiv k A).symm x
      = x.fst ⊗ₜ[k] (1 : DualNumber k) + x.snd ⊗ₜ[k] (ε : DualNumber k) := by
  apply (baseChangeAlgEquiv k A).injective
  rw [AlgEquiv.apply_symm_apply, map_add, baseChangeAlgEquiv_tmul,
    baseChangeAlgEquiv_tmul]
  refine (TrivSqZeroExt.ext ?_ ?_).symm <;> simp [smul_eq_mul]

end BaseChange

end DualNumber
