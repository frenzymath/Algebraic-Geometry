/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.RiemannRoch.Adelic.NonconstantToP1
import AlgebraicJacobian.Picard.HasRationalPoint
import AlgebraicJacobian.Picard.RigidPushforward
import AlgebraicJacobian.Picard.SectionRingUniversal

/-!
# Base change of the AJC curve along a field extension (Λ-stability substrate)

For a field extension `κ/k` (with structure map
`φ := Spec.map (CommRingCat.ofHom (algebraMap k κ))`) and an AJC curve
`C : Over (Spec k)` — `[SmoothOfRelativeDimension 1 C.hom]`, `[IsProper C.hom]`,
`[GeometricallyIntegral C.hom]` — this file provides the **named** base-changed
curve `Scheme.baseChangeField C κ := Over.mk (pullback.snd C.hom φ)` together
with **named instances** (so that use sites need no inline `haveI` blocks)
showing that `C_κ` is again an AJC curve over `κ`:

* `smoothOfRelativeDimension_one_hom_baseChangeField`,
  `isProper_hom_baseChangeField`, `geometricallyIntegral_hom_baseChangeField` —
  the three defining curve properties are stable under the base change;
* `hasRationalPoint_baseChangeField` — a `k`-rational point base-changes to a
  `κ`-rational point (base change of the section);
* the total-space substrate needed by the scoped adelic gate discharge
  `Scheme.instIsConstantField` (`RiemannRoch/Adelic/GateInstances.lean`):
  `isIntegral_left_baseChangeField`, `isLocallyNoetherian_left_baseChangeField`,
  `isRegularInCodimensionOne_left_baseChangeField`, obtained by specialising
  general-curve substrate instances over an arbitrary base field
  (`isIntegral_left_of_geometricallyIntegral`, reused from
  `Picard/SectionRingUniversal.lean`; `isLocallyNoetherian_left_of_locallyOfFiniteType`
  and `isRegularInCodimensionOne_left_of_curve`, stated here);
* `AffineCoverMVSquare.baseChangeField` — the 2-affine Mayer–Vietoris cover of
  `C_κ` obtained by pulling a cover of `C` back along the (affine) first
  projection, reusing `AffineCoverMVSquare.preimage`
  (`Picard/RigidPushforward.lean`), with the chart-identification `simp` lemmas.

**On geometric integrality.** `AlgebraicGeometry.GeometricallyIntegral` is
the Mathlib class (`Mathlib/AlgebraicGeometry/Geometrically/Integral.lean`):
`f : X ⟶ Y` is geometrically integral iff `geometrically IsIntegral f`, i.e.
for every field `K`, every `y : Spec K ⟶ Y`, and every pullback square of `f`
along `y`, the total space is integral — exactly "fibres integral after
arbitrary field extension". Stability of this property under a field
extension, which is transitivity of base change, is therefore already
available as
`MorphismProperty.IsStableUnderBaseChange @GeometricallyIntegral` together
with the direct instance `GeometricallyIntegral (pullback.snd f g)`; the
named instance below is a re-export keyed on the `baseChangeField` spelling,
not a re-proof.

The general-curve regularity instance
`isRegularInCodimensionOne_left_of_curve` is the genuinely new content: over an
*arbitrary* base field `k`, every codimension-one stalk of the AJC curve is a
DVR. The proof descends the property from the base change to the algebraic
closure `k̄` (where `Scheme.localRing_dvr_of_codim_one`,
`Albanese/CodimOneExtension.lean`, applies) along the faithfully flat stalk
map: the valuation-ring dichotomy descends by
`Adelic.mem_range_algebraMap_or_inv_mem_range`
(`RiemannRoch/Adelic/NonconstantToP1.lean`), and a noetherian local domain
that is a valuation ring and not a field is a DVR
(`IsDiscreteValuationRing.TFAE`). This is the same descent skeleton as the
valuative dichotomy `regLocus_sup_regLocus_inv_eq_top` of `NonconstantToP1.lean`
(which is `private` there), repackaged per-stalk as reusable substrate.
-/

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry

namespace Scheme

variable {k : Type u} [Field k]

/-! ## §1. General-curve total-space substrate over an arbitrary field -/

section CurveSubstrate

variable (C : Over (Spec (CommRingCat.of k)))

/- Integrality of the total space (`IsIntegral C.left` from
`[GeometricallyIntegral C.hom]`) is already provided by the named instance
`Scheme.isIntegral_left_of_geometricallyIntegral` of
`Picard/SectionRingUniversal.lean` (imported above); it is reused here, not
redefined (name-collision discipline). -/

/-- **The total space of a locally-finite-type scheme over a field is locally
noetherian** (`LocallyOfFiniteType.isLocallyNoetherian` over the noetherian
base `Spec k`). Named substrate instance for the adelic gate
`Scheme.instIsConstantField`. -/
instance (priority := low) isLocallyNoetherian_left_of_locallyOfFiniteType
    [LocallyOfFiniteType C.hom] : IsLocallyNoetherian C.left :=
  haveI : IsNoetherianRing (CommRingCat.of k) := inferInstanceAs (IsNoetherianRing k)
  LocallyOfFiniteType.isLocallyNoetherian C.hom

/-- **The AJC curve is regular in codimension one, over an arbitrary base
field** (Hartshorne's condition `(*)`, third clause): every prime-divisor
stalk of the total space is a DVR.

Over an algebraically closed field this is
`Scheme.localRing_dvr_of_codim_one` (`Albanese/CodimOneExtension.lean`,
smooth ⟹ regular, Stacks 00TT). Over an arbitrary `k` the property
*descends* from the base change `C_{k̄} = C ×_k k̄` along the faithfully flat
stalk map at a point `z'` over the given point `w`: the stalk upstairs is a
DVR (its maximal ideal is nonzero because the nonzero maximal ideal downstairs
maps into it injectively, so its coheight is exactly `1` by
`coheight_le_one_of_curve`), hence a valuation ring, the valuation dichotomy
descends by `Adelic.mem_range_algebraMap_or_inv_mem_range`
(faithfully flat divisibility descent), and a noetherian local domain that is
a valuation ring and not a field is a DVR (`IsDiscreteValuationRing.TFAE`).
The stalk downstairs is not a field since its Krull dimension is the coheight
`1` of the prime divisor (`Scheme.ringKrullDim_stalk_eq_coheight`). -/
instance (priority := low) isRegularInCodimensionOne_left_of_curve
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [IsIntegral C.left] :
    Scheme.IsRegularInCodimensionOne C.left := by
  haveI : Smooth C.hom := SmoothOfRelativeDimension.smooth 1 C.hom
  haveI : IsNoetherianRing (CommRingCat.of k) := inferInstanceAs (IsNoetherianRing k)
  haveI : IsLocallyNoetherian C.left := LocallyOfFiniteType.isLocallyNoetherian C.hom
  refine ⟨fun Y => ?_⟩
  -- the base change to the algebraic closure and its (surjective, flat) projection
  haveI : Subsingleton (Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  haveI : Nonempty (Spec (CommRingCat.of (AlgebraicClosure k))) :=
    inferInstanceAs (Nonempty (PrimeSpectrum (AlgebraicClosure k)))
  set y : Spec (CommRingCat.of (AlgebraicClosure k)) ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))) with hy
  haveI : Surjective y := ⟨fun _ => ⟨Nonempty.some ‹_›, Subsingleton.elim _ _⟩⟩
  haveI : Flat y := by
    rw [hy, AlgebraicGeometry.Flat.SpecMap_iff, CommRingCat.hom_ofHom,
      RingHom.flat_algebraMap_iff]
    infer_instance
  set p := pullback.fst C.hom y with hp
  haveI : Surjective p := by rw [hp]; infer_instance
  haveI : Flat p := by rw [hp]; infer_instance
  obtain ⟨z', hz'⟩ := p.surjective Y.point
  rw [← hz']
  have hcoh : Order.coheight (p z') = 1 := by rw [hz']; exact Y.coheight
  -- the stalk downstairs: noetherian local domain of Krull dimension 1, not a field
  have hdimA : ringKrullDim (C.left.presheaf.stalk (p z')) = 1 := by
    rw [Scheme.ringKrullDim_stalk_eq_coheight]
    exact_mod_cast hcoh
  have hnfA : ¬ IsField (C.left.presheaf.stalk (p z')) := by
    intro hF
    have h0 : ringKrullDim (C.left.presheaf.stalk (p z')) = 0 :=
      ringKrullDim_eq_zero_of_isField hF
    rw [hdimA] at h0
    exact_mod_cast h0
  have hmA : IsLocalRing.maximalIdeal (C.left.presheaf.stalk (p z')) ≠ ⊥ :=
    fun h => hnfA (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h)
  -- ambient instances on the base-changed curve
  haveI hCbInt : IsIntegral (pullback C.hom y) :=
    GeometricallyIntegral.geometrically_isIntegral (f := C.hom) y
      (pullback.fst C.hom y) (pullback.snd C.hom y) (IsPullback.of_hasPullback C.hom y)
  haveI : IsIntegral (Over.mk (pullback.snd C.hom y)).left := hCbInt
  haveI : IsReduced (Over.mk (pullback.snd C.hom y)).left :=
    inferInstanceAs (IsReduced (pullback C.hom y))
  haveI : Smooth (Over.mk (pullback.snd C.hom y)).hom :=
    MorphismProperty.pullback_snd _ _ ‹Smooth C.hom›
  haveI : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  haveI : SmoothOfRelativeDimension 1 (Over.mk (pullback.snd C.hom y)).hom :=
    MorphismProperty.pullback_snd _ _ ‹SmoothOfRelativeDimension 1 C.hom›
  haveI : GeometricallyIrreducible (Over.mk (pullback.snd C.hom y)).hom :=
    MorphismProperty.pullback_snd _ _ (inferInstance : GeometricallyIrreducible C.hom)
  haveI : IsSeparated (Over.mk (pullback.snd C.hom y)).hom :=
    MorphismProperty.pullback_snd _ _ (inferInstance : IsSeparated C.hom)
  haveI : LocallyOfFiniteType (Over.mk (pullback.snd C.hom y)).hom :=
    MorphismProperty.pullback_snd _ _ (inferInstance : LocallyOfFiniteType C.hom)
  -- the faithfully flat local stalk map at `z'`
  have hφflat : ((p.stalkMap z').hom).Flat := AlgebraicGeometry.Flat.stalkMap p z'
  letI : Algebra (C.left.presheaf.stalk (p z'))
      ((pullback C.hom y).presheaf.stalk z') := ((p.stalkMap z').hom).toAlgebra
  haveI : Module.Flat (C.left.presheaf.stalk (p z'))
      ((pullback C.hom y).presheaf.stalk z') := hφflat
  haveI : IsLocalHom (algebraMap (C.left.presheaf.stalk (p z'))
      ((pullback C.hom y).presheaf.stalk z')) :=
    inferInstanceAs (IsLocalHom ((p.stalkMap z').hom))
  haveI : Module.FaithfullyFlat (C.left.presheaf.stalk (p z'))
      ((pullback C.hom y).presheaf.stalk z') :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  -- the maximal ideal upstairs is nonzero: push a nonzero `π ∈ m_A` up
  obtain ⟨π, hπm, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hmA
  have hπB0 : (p.stalkMap z').hom π ≠ 0 := fun h0 =>
    hπ0 (FaithfulSMul.algebraMap_injective (C.left.presheaf.stalk (p z'))
      ((pullback C.hom y).presheaf.stalk z')
      (show algebraMap _ _ π = algebraMap _ _ 0 by rw [map_zero]; exact h0))
  have hπBm : (p.stalkMap z').hom π ∈
      IsLocalRing.maximalIdeal ((pullback C.hom y).presheaf.stalk z') := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal π).mp hπm)
      (isUnit_of_map_unit ((p.stalkMap z').hom) π hu)
  have hmB : IsLocalRing.maximalIdeal ((pullback C.hom y).presheaf.stalk z') ≠ ⊥ := by
    intro hbot
    rw [hbot] at hπBm
    exact hπB0 (Submodule.mem_bot _ |>.mp hπBm)
  -- the stalk upstairs is a codimension-one DVR
  have hcohB : Order.coheight z' = 1 := by
    have hle := Adelic.coheight_le_one_of_curve (Over.mk (pullback.snd C.hom y)) z'
    have hne0 : Order.coheight z' ≠ 0 := by
      intro h0
      have hdim0 : ringKrullDim ((pullback C.hom y).presheaf.stalk z') = 0 := by
        rw [Scheme.ringKrullDim_stalk_eq_coheight, h0]
        rfl
      haveI : Ring.KrullDimLE 0 ((pullback C.hom y).presheaf.stalk z') :=
        Ring.krullDimLE_iff.mpr (le_of_eq hdim0)
      have hbotmax : (⊥ : Ideal ((pullback C.hom y).presheaf.stalk z')).IsMaximal :=
        Ideal.isPrime_bot.isMaximal'
      exact hmB (IsLocalRing.eq_maximalIdeal hbotmax).symm
    exact le_antisymm hle (Order.one_le_iff_ne_zero.mpr hne0)
  have hDVR : IsDiscreteValuationRing ((pullback C.hom y).presheaf.stalk z') :=
    Scheme.localRing_dvr_of_codim_one (X := Over.mk (pullback.snd C.hom y)) z' hcohB
  haveI := hDVR
  haveI : ValuationRing ((pullback C.hom y).presheaf.stalk z') := inferInstance
  -- descend the valuation dichotomy along the faithfully flat stalk map …
  haveI hVR : ValuationRing (C.left.presheaf.stalk (p z')) := by
    rw [ValuationRing.iff_isInteger_or_isInteger _
      (FractionRing (C.left.presheaf.stalk (p z')))]
    intro t
    by_cases ht : t = 0
    · exact Or.inl ⟨0, by rw [map_zero, ht]⟩
    rcases Adelic.mem_range_algebraMap_or_inv_mem_range
        (A := ((C.left.presheaf.stalk (p z') : CommRingCat) : Type u))
        (K := FractionRing ((C.left.presheaf.stalk (p z') : CommRingCat) : Type u))
        (B := (((pullback C.hom y).presheaf.stalk z' : CommRingCat) : Type u))
        (L := FractionRing (((pullback C.hom y).presheaf.stalk z' : CommRingCat) : Type u))
        t ht with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact Or.inl ⟨a, ha⟩
    · exact Or.inr ⟨a, ha⟩
  -- … and conclude: noetherian local domain + valuation ring + not a field ⇒ DVR
  exact ((IsDiscreteValuationRing.TFAE (C.left.presheaf.stalk (p z')) hnfA).out 1 0).mp hVR

end CurveSubstrate

/-! ## §2. The base-changed curve and its named curve-package instances -/

section BaseChangeField

variable (C : Over (Spec (CommRingCat.of k))) (κ : Type u) [Field κ] [Algebra k κ]

/-- **The base change of a `k`-scheme `C` along a field extension `κ/k`**:
`C_κ := C ×_{Spec k} Spec κ`, as an object of `Over (Spec κ)` via the second
projection. The named carrier of the Λ-stability instances below (instances
are keyed on this definitional spelling). -/
noncomputable def baseChangeField : Over (Spec (CommRingCat.of κ)) :=
  Over.mk (pullback.snd C.hom (Spec.map (CommRingCat.ofHom (algebraMap k κ))))

/-- Smoothness of relative dimension `1` is stable under the field base change
(`smoothOfRelativeDimension_isStableUnderBaseChange`, extraction of the inline
recipe at `RiemannRoch/Adelic/NonconstantToP1.lean:986-989`). -/
instance smoothOfRelativeDimension_one_hom_baseChangeField
    [SmoothOfRelativeDimension 1 C.hom] :
    SmoothOfRelativeDimension 1 (baseChangeField C κ).hom :=
  haveI : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  MorphismProperty.pullback_snd _ _ ‹SmoothOfRelativeDimension 1 C.hom›

/-- Properness is stable under the field base change (Mathlib
`IsProper.isStableUnderBaseChange`). -/
instance isProper_hom_baseChangeField [IsProper C.hom] :
    IsProper (baseChangeField C κ).hom :=
  MorphismProperty.pullback_snd _ _ ‹IsProper C.hom›

/-- Geometric integrality is stable under the field base change. **Audit item
6** (see the module docstring): the in-tree `GeometricallyIntegral` is the
Mathlib class "every field-valued base change of `f` has integral total
space", and its stability under arbitrary base change — a fortiori under the
field extension `φ : Spec κ ⟶ Spec k`, by transitivity of base change — is
already provided by Mathlib
(`MorphismProperty.IsStableUnderBaseChange @GeometricallyIntegral`); this
named instance re-exports it keyed on the `baseChangeField` spelling. -/
instance geometricallyIntegral_hom_baseChangeField [GeometricallyIntegral C.hom] :
    GeometricallyIntegral (baseChangeField C κ).hom :=
  MorphismProperty.pullback_snd _ _ ‹GeometricallyIntegral C.hom›

/-- **A rational point base-changes**: a section `σ` of `C.hom` lifts to the
section `pullback.lift (φ ≫ σ) (𝟙 _)` of the base-changed structure morphism
(pattern `IdentityComponent.baseChangeIso`, `Picard/IdentityComponent.lean`,
specialised to the section rather than the group structure). -/
instance hasRationalPoint_baseChangeField [HasRationalPoint C] :
    HasRationalPoint (baseChangeField C κ) := by
  obtain ⟨⟨σ, hσ⟩⟩ := HasRationalPoint.nonempty_section (C := C)
  refine ⟨⟨⟨pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap k κ)) ≫ σ) (𝟙 _) ?_, ?_⟩⟩⟩
  · rw [Category.assoc, hσ, Category.comp_id, Category.id_comp]
  · exact pullback.lift_snd _ _ _

/-- The total space of the base-changed curve is integral (named substrate
instance for the adelic gate `Scheme.instIsConstantField` on `C_κ`). -/
instance isIntegral_left_baseChangeField [GeometricallyIntegral C.hom] :
    IsIntegral (baseChangeField C κ).left :=
  isIntegral_left_of_geometricallyIntegral (baseChangeField C κ)

/-- The total space of the base-changed curve is locally noetherian (named
substrate instance for the adelic gate `Scheme.instIsConstantField` on `C_κ`). -/
instance isLocallyNoetherian_left_baseChangeField [IsProper C.hom] :
    IsLocallyNoetherian (baseChangeField C κ).left :=
  isLocallyNoetherian_left_of_locallyOfFiniteType (baseChangeField C κ)

/-- The total space of the base-changed curve is regular in codimension one
(named substrate instance for the adelic gate `Scheme.instIsConstantField` on
`C_κ`; specialisation of the arbitrary-field curve regularity
`isRegularInCodimensionOne_left_of_curve`). -/
instance isRegularInCodimensionOne_left_baseChangeField
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIntegral C.hom] :
    Scheme.IsRegularInCodimensionOne (baseChangeField C κ).left :=
  isRegularInCodimensionOne_left_of_curve (baseChangeField C κ)

end BaseChangeField

/-! ## §3. Base change of a 2-affine Mayer–Vietoris cover square -/

section CoverBaseChange

variable (C : Over (Spec (CommRingCat.of k))) (κ : Type u) [Field κ] [Algebra k κ]

/-- The first projection `C_κ ⟶ C` of the field base change is an affine
morphism: it is the base change of the affine `Spec κ ⟶ Spec k` (pattern
`isAffineHom_p1BaseChange_fst`, `Picard/RigidPushforward.lean`). -/
instance isAffineHom_baseChangeField_fst :
    IsAffineHom (pullback.fst C.hom (Spec.map (CommRingCat.ofHom (algebraMap k κ)))) :=
  MorphismProperty.pullback_fst (P := @IsAffineHom) C.hom
    (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
    (inferInstance : IsAffineHom (Spec.map (CommRingCat.ofHom (algebraMap k κ))))

variable {C}

/-- **A 2-affine Mayer–Vietoris cover square base-changes along a field
extension**: the preimage (`AffineCoverMVSquare.preimage`,
`Picard/RigidPushforward.lean`) of a bundled 2-affine cover of `C` under the
affine first projection `C_κ ⟶ C`. Charts are identified by
`baseChangeField_U₁`/`baseChangeField_U₂`. Companion of
`AffineCoverMVSquare.baseChangeSpecOver` (`Picard/FinitePresentationFunctor.lean`),
which is keyed on the `specOver k A` base shape; this one is keyed on the raw
`Spec.map (algebraMap k κ)` spelling. -/
noncomputable def AffineCoverMVSquare.baseChangeField
    (S : C.left.AffineCoverMVSquare) :
    (Scheme.baseChangeField C κ).left.AffineCoverMVSquare :=
  show (pullback C.hom (Spec.map (CommRingCat.ofHom (algebraMap k κ)))).AffineCoverMVSquare from
    S.preimage (pullback.fst C.hom (Spec.map (CommRingCat.ofHom (algebraMap k κ))))

/-- Chart identification for the base-changed cover square: the first chart is
the preimage of the first chart. -/
@[simp] lemma AffineCoverMVSquare.baseChangeField_U₁ (S : C.left.AffineCoverMVSquare) :
    (S.baseChangeField κ).U₁ =
      pullback.fst C.hom (Spec.map (CommRingCat.ofHom (algebraMap k κ))) ⁻¹ᵁ S.U₁ :=
  rfl

/-- Chart identification for the base-changed cover square: the second chart is
the preimage of the second chart. -/
@[simp] lemma AffineCoverMVSquare.baseChangeField_U₂ (S : C.left.AffineCoverMVSquare) :
    (S.baseChangeField κ).U₂ =
      pullback.fst C.hom (Spec.map (CommRingCat.ofHom (algebraMap k κ))) ⁻¹ᵁ S.U₂ :=
  rfl

end CoverBaseChange

end Scheme

end AlgebraicGeometry
