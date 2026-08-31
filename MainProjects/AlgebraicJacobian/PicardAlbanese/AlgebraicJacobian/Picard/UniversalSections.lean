/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.SectionsBaseChange
import AlgebraicJacobian.Curve.Sections
import AlgebraicJacobian.Curve.GeometricallyReduced

/-!
# Universal sections: `Γ((C ⊗ Spec A).left, 𝒪) = A` for every `k`-algebra `A`

Brick 2 of the separatedness ledger (design §4.4): for the proper, geometrically integral
curve `C` over the field `k` and **every** commutative `k`-algebra `A`, the second
projection induces an isomorphism `A ≅ Γ((C ⊗ Spec A).left, ⊤)`. This is the form of
Kleiman's `ex:gc&r` ("`𝒪_S ≅ f_*𝒪_X` holds universally", *The Picard Scheme* §3.11)
actually consumed downstream: by the étale-separatedness argument (C1), by the
dual-numbers tangent engine (`A = k[ε]`), and by the χ-ledger over field extensions
(`A = K`).

## Main declarations

* `AlgebraicGeometry.Over.isIso_appTop_snd_overSpec` — the keystone: the pullback of global
  sections along the second projection, `Γ(Spec A, ⊤) ⟶ Γ((C ⊗ overSpec k A).left, ⊤)`,
  is an isomorphism.
* `AlgebraicGeometry.Over.universalSections` — the bundled form
  `CommRingCat.of A ≅ Γ((C ⊗ overSpec k A).left, ⊤)`; its `hom` is by definition the
  `A`-algebra structure map of the global sections of the base change induced by the
  second projection (the `A`-algebra face of the statement).
* `AlgebraicGeometry.Over.universalSectionsEquiv` — the same as a ring equivalence
  `A ≃+* Γ((C ⊗ overSpec k A).left, ⊤)`.
* `AlgebraicGeometry.Over.universalSections_self` — the **consistency gate** (design §7.2,
  lane L3): at `A := k` the isomorphism is Wave 1's `Γ(C.left, 𝒪) ≅ k`
  (`AlgebraicGeometry.isIso_hom_appTop_of_geometricallyReduced`, `Curve/Sections.lean`)
  transported along the first projection — which is an isomorphism because
  `Spec k ⟶ Spec k` is.

## Proof route

`⊤ ⊆ C.left` is quasi-compact (properness) and quasi-separated (separatedness), so the
qcqs master square `AlgebraicGeometry.Over.isPushout_sections` (brick 1, via mathlib's
`pushoutSection` API — this replaces the hand-rolled two-cover equalizer ladder foreseen
by the design, which mathlib's `isIso_pushoutSection_of_isQuasiSeparated_of_flat_right`
already contains) exhibits `Γ((C ⊗ Spec A).left, ⊤)` as the pushout of
`Γ(Spec k, ⊤) ⟶ Γ(C.left, ⊤)` and `Γ(Spec k, ⊤) ⟶ Γ(Spec A, ⊤)`. The first leg is an
isomorphism by Wave 1's `Γ(C.left, 𝒪) ≅ k`, and a pushout of an isomorphism is an
isomorphism, so the second projection leg is one too.

Hypotheses: the theorems are stated with the honest hypotheses `[IsProper C.hom]`,
`[GeometricallyIrreducible C.hom]`, `[GeometricallyReduced C.hom]` (mirroring
`Curve/Sections.lean`); for the curve bundle of the challenge, geometric reducedness is
automatic from smoothness (`Smooth.geometricallyReduced`) — see the regression checks at
the bottom of the file.

Brick 3 of the ledger, `Over.prPullback_injective` (injectivity of
`CechPic.map (snd C T).left`, for **arbitrary** `T`), lives in
`AlgebraicJacobian.Picard.Separatedness`; its section-level engine
`Over.isIso_appLE_snd` generalizes `Over.isIso_appTop_snd_overSpec` below from
`(T, V) = (Spec A, ⊤)` to any `T` and any affine open `V ⊆ T.left`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

section UniversalSections

variable (C : Over (Spec (.of k)))
  [IsProper C.hom] [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]
variable (A : Type u) [CommRing A] [Algebra k A]

/-- **Universal triviality of global sections** (Kleiman `ex:gc&r` in consumable form):
for `C` proper, geometrically irreducible and geometrically reduced over the field `k`,
and any commutative `k`-algebra `A`, pullback of global sections along the second
projection `(C ⊗ Spec A).left ⟶ Spec A` is an isomorphism. -/
theorem Over.isIso_appTop_snd_overSpec :
    IsIso ((snd C (overSpec k A)).left.appTop) := by
  -- `⊤ ⊆ C.left` is quasi-compact and quasi-separated, since `C` is proper over a field.
  have hV : IsCompact ((⊤ : C.left.Opens) : Set C.left) := by
    have : CompactSpace C.left := QuasiCompact.compactSpace_of_compactSpace C.hom
    simpa using CompactSpace.isCompact_univ
  have hV' : IsQuasiSeparated ((⊤ : C.left.Opens) : Set C.left) := by
    have : QuasiSeparatedSpace C.left := quasiSeparatedSpace_of_quasiSeparated C.hom
    simpa using isQuasiSeparated_univ
  -- Brick 1: `Γ((C ⊗ Spec A).left, ⊤)` is the pushout of the two section maps.
  have hp := Over.isPushout_sections C (overSpec k A) (isAffineOpen_top_overSpec k A) hV hV'
  -- Wave 1: the `C`-side leg `Γ(Spec k, ⊤) ⟶ Γ(C.left, ⊤)` is an isomorphism.
  haveI : IsIso (C.hom.appLE ⊤ (⊤ : C.left.Opens)
      (le_top.trans (Scheme.Hom.preimage_top C.hom).ge)) := by
    have h : C.hom.appLE ⊤ (⊤ : C.left.Opens)
        (le_top.trans (Scheme.Hom.preimage_top C.hom).ge) = C.hom.appTop :=
      Scheme.Hom.appLE_eq_app C.hom
    rw [h]
    infer_instance
  -- A pushout of an isomorphism is an isomorphism: compare with the trivial square.
  have htriv : IsPushout
      (C.hom.appLE ⊤ (⊤ : C.left.Opens) (le_top.trans (Scheme.Hom.preimage_top C.hom).ge))
      ((overSpec k A).hom.appLE ⊤ ⊤ (Scheme.Hom.preimage_top (overSpec k A).hom).ge)
      (inv (C.hom.appLE ⊤ (⊤ : C.left.Opens)
          (le_top.trans (Scheme.Hom.preimage_top C.hom).ge)) ≫
        (overSpec k A).hom.appLE ⊤ ⊤ (Scheme.Hom.preimage_top (overSpec k A).hom).ge)
      (𝟙 _) :=
    IsPushout.of_horiz_isIso ⟨by rw [IsIso.hom_inv_id_assoc, Category.comp_id]⟩
  have h2 := hp.inr_isoIsPushout_hom _ _ htriv
  rw [Iso.comp_hom_eq_id] at h2
  have key : (snd C (overSpec k A)).left.appLE ⊤ ((fst C (overSpec k A)).left ⁻¹ᵁ ⊤)
      (le_top.trans (Scheme.Hom.preimage_top (snd C (overSpec k A)).left).ge) =
      (snd C (overSpec k A)).left.appTop :=
    Scheme.Hom.appLE_eq_app _
  rw [← key, h2]
  infer_instance

/-- **Universal sections** (brick 2 of the separatedness ledger, design §4.4):
`Γ((C ⊗ Spec A).left, 𝒪) = A` for every commutative `k`-algebra `A`. The `hom` direction
is `A ≅ Γ(Spec A, ⊤)` followed by pullback along the second projection, i.e. it is the
canonical `A`-algebra structure map of the global sections of the base change. -/
noncomputable def Over.universalSections :
    CommRingCat.of A ≅ Γ((C ⊗ overSpec k A).left, ⊤) :=
  (Scheme.ΓSpecIso (.of A)).symm ≪≫
    @asIso _ _ _ _ _ (Over.isIso_appTop_snd_overSpec C A)

/-- `Γ((C ⊗ Spec A).left, 𝒪) = A`, as a ring equivalence. -/
noncomputable def Over.universalSectionsEquiv :
    A ≃+* Γ((C ⊗ overSpec k A).left, ⊤) :=
  (Over.universalSections C A).commRingCatIsoToRingEquiv

end UniversalSections

section ConsistencyGate

/-- `Spec k ⟶ Spec k` (as the structure morphism of `overSpec k k`) is an isomorphism. -/
instance isIso_overSpec_self_hom : IsIso (overSpec k k).hom := by
  rw [overSpec_hom, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  exact IsIso.id _

variable (C : Over (Spec (.of k)))

/-- The first projection `(C ⊗ Spec k).left ⟶ C.left` is an isomorphism: it is the
pullback of the isomorphism `Spec k ⟶ Spec k`. -/
instance isIso_fst_left_overSpec_self : IsIso (fst C (overSpec k k)).left := by
  rw [Over.fst_left]
  exact pullback_fst_iso_of_right_iso _ _

/-- Pullback of global sections along the (iso) first projection at `A := k`. -/
instance isIso_appTop_fst_left_overSpec_self :
    IsIso ((fst C (overSpec k k)).left.appTop) := by
  refine ⟨⟨(inv (fst C (overSpec k k)).left).appTop, ?_, ?_⟩⟩
  · rw [← Scheme.Hom.comp_appTop, IsIso.inv_hom_id, Scheme.Hom.id_appTop]
  · rw [← Scheme.Hom.comp_appTop, IsIso.hom_inv_id, Scheme.Hom.id_appTop]

variable [IsProper C.hom] [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]

/-- **Consistency gate for lane L3** (design §7.2): at `A := k`, the universal-sections
isomorphism `k ≅ Γ((C ⊗ Spec k).left, ⊤)` is exactly Wave 1's isomorphism
`k ≅ Γ(C.left, 𝒪)` (`(Scheme.ΓSpecIso _).symm ≪≫ asIso C.hom.appTop`, cf. the regression
check of `Curve/Sections.lean`) transported to the product along the first projection. -/
theorem Over.universalSections_self :
    Over.universalSections C k =
      ((Scheme.ΓSpecIso (.of k)).symm ≪≫ asIso C.hom.appTop) ≪≫
        asIso ((fst C (overSpec k k)).left.appTop) := by
  refine Iso.ext ?_
  simp only [Over.universalSections, Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc]
  have hk : (overSpec k k).hom.appTop = 𝟙 _ := by
    rw [overSpec_hom, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id,
      Scheme.Hom.id_appTop]
  rw [cancel_epi, ← Scheme.Hom.comp_appTop, (Over.isPullback_left C (overSpec k k)).w,
    Scheme.Hom.comp_appTop, hk]
  exact (Category.id_comp _).symm

end ConsistencyGate

section RegressionChecks

/-! For the curve bundle of the challenge (smooth, proper, geometrically irreducible),
geometric reducedness — and hence every hypothesis above — is automatic. -/

variable {C : Over (Spec (.of k))}
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
variable (A : Type u) [CommRing A] [Algebra k A]

example : IsIso ((snd C (overSpec k A)).left.appTop) :=
  Over.isIso_appTop_snd_overSpec C A

noncomputable example : CommRingCat.of A ≅ Γ((C ⊗ overSpec k A).left, ⊤) :=
  Over.universalSections C A

end RegressionChecks

end AlgebraicGeometry
