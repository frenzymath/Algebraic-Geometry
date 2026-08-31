/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Descent.GaloisSelfTensor

/-!
# The Galois graph cover of the field-extension kernel pair

Ported from the sibling Algebraic Jacobian project.  This file collects, from
several AJC modules, exactly the fragments the finite Galois quotient engine
needs to run effective descent along `Spec L ⟶ Spec K`:

* from `AlgebraicJacobian.Picard.EtaleFieldCover`: the étale-algebra instance
  for a finite separable field extension, and (surjectivity/étaleness of)
  `Spec k' ⟶ Spec k` together with its base change `pullback.fst`;
* from `AlgebraicJacobian.Picard.PicEtCrossBase` /
  `AlgebraicJacobian.Picard.PicEtDescentAssembly`: the slice-category
  vocabulary `specMapAlgebra`, `restrictTest`, `baseTest`, `coverMap`;
* from `AlgebraicJacobian.Picard.GaloisDescent.PicEtGaloisBridge`: the
  `γ`-twist `twistLeft`/`twistTest`, the graph sections `coverSelfSection` of
  the cover's self-pullback, and the `Gal`-indexed coproduct splitting
  `selfTensorSpecCoproduct` of `Spec (k' ⊗[k] k')`;
* from `AlgebraicJacobian.Picard.PicEtDescentExistence`: the evaluation of the
  Galois splitting on the two tensor inclusions;
* from `AlgebraicJacobian.Picard.GaloisDescent.PicEtGaloisCover`: étaleness /
  open-immersionness of the graph sections;
* from `AlgebraicJacobian.Picard.GaloisDescent.GaloisKernelCover`: the
  `Gal`-indexed open cover of the kernel pair of
  `pullback.fst t (Spec.map (algebraMap k k'))` and the resulting hom
  extensionality `coverSelfSection_hom_ext`.

None of the `picEt` sheaf theory is ported; the étale-topology membership
statements of the original files are omitted as the quotient engine does not
consume them.

The mathematical content: for finite Galois `k'/k`, the self-pullback
`Spec k' ×_{Spec k} Spec k'` is `Gal(k'/k)` copies of `Spec k'`
(`galoisSelfTensorEquiv` read through `Spec`), so the kernel pair of a
base-changed field cover is covered by the `Gal`-indexed graph sections
`⟨𝟙, twist γ⟩` — which is what turns `Γ`-invariance of a morphism into descent
data along the cover.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme

section Algebra

variable (k k' : Type u) [Field k] [Field k'] [Algebra k k']
  [Algebra.IsSeparable k k'] [Module.Finite k k']

/-- **A finite separable field extension is an étale algebra.**

Formal étaleness is separability (`Algebra.FormallyEtale.of_isSeparable`), and
finite presentation follows from finite type over a field
(`Algebra.FinitePresentation.of_finiteType`, the Noetherian criterion).

Stated as an `instance` because both inputs are, and because
`Algebra.Etale k k'` does *not* synthesize without it: this is the declaration
whose absence makes the étale cover below look unavailable. -/
instance etale_of_finite_isSeparable : Algebra.Etale k k' where
  formallyEtale := Algebra.FormallyEtale.of_isSeparable k k'
  finitePresentation :=
    (Algebra.FinitePresentation.of_finiteType (R := k) (A := k')).mp inferInstance

end Algebra

section Cover

variable (k k' : Type u) [Field k] [Field k'] [Algebra k k']

/-- **`Spec k' ⟶ Spec k` is surjective on points**, for *any* extension of
fields: both spectra have exactly one point, so this needs neither separability
nor finiteness.

Stated on the underlying map because that is the form
`Scheme.singleton_mem_precoverage_iff` consumes; the morphism-property version is
`surjective_specMap_algebraMap` below. -/
theorem surjective_base_specMap_algebraMap :
    Function.Surjective (Spec.map (CommRingCat.ofHom (algebraMap k k'))).base :=
  fun _ => ⟨default, Subsingleton.elim _ _⟩

/-- `Spec k' ⟶ Spec k` is surjective as a morphism property. -/
theorem surjective_specMap_algebraMap :
    Surjective (Spec.map (CommRingCat.ofHom (algebraMap k k'))) :=
  ⟨surjective_base_specMap_algebraMap k k'⟩

variable [Algebra.IsSeparable k k'] [Module.Finite k k']

/-- **`Spec k' ⟶ Spec k` is étale** for `k'/k` finite separable.

The bridge from the algebra statement of §1 to the morphism property is
`RingHom.etale_algebraMap` followed by `HasRingHomProperty.Spec_iff`. It is
needed because `Etale (Spec.map …)` does not synthesize: `RingHom.Etale f` is
`Algebra.Etale` at `f.toAlgebra`, which is not the ambient `Algebra k k'`
instance up to reducible defeq. -/
theorem etale_specMap_algebraMap :
    Etale (Spec.map (CommRingCat.ofHom (algebraMap k k'))) :=
  (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (RingHom.etale_algebraMap.mpr inferInstance)

end Cover

section BaseChange

variable (k k' : Type u) [Field k] [Field k'] [Algebra k k']
  [Algebra.IsSeparable k k'] [Module.Finite k k']

/-- **The base-changed cover is étale.** `Etale` is stable under base change in
Mathlib (`AlgebraicGeometry.Etale.etale_isStableUnderBaseChange`), so this needs
no argument beyond §2 — recorded because it is the form `G1`'s spreading step
consumes, at an arbitrary test object rather than at `Spec k`. -/
theorem etale_pullback_fst_specMap (T : Scheme.{u}) (a : T ⟶ Spec (CommRingCat.of k)) :
    Etale (pullback.fst a (Spec.map (CommRingCat.ofHom (algebraMap k k')))) :=
  haveI := etale_specMap_algebraMap k k'
  inferInstance

omit [Algebra.IsSeparable k k'] [Module.Finite k k'] in
/-- **The base-changed cover is surjective**, so it is again a cover. Together
with `etale_pullback_fst_specMap` this says the field-extension cover pulls back
to an étale cover of every `k`-scheme.

Needs neither separability nor finiteness, for the same reason
`surjective_base_specMap_algebraMap` does not. -/
theorem surjective_pullback_fst_specMap (T : Scheme.{u})
    (a : T ⟶ Spec (CommRingCat.of k)) :
    Surjective (pullback.fst a (Spec.map (CommRingCat.ofHom (algebraMap k k')))) :=
  haveI := surjective_specMap_algebraMap k k'
  inferInstance

end BaseChange


namespace PicScheme

open scoped TensorProduct

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']

/-- The structural morphism `Spec k' ⟶ Spec k` of a field extension. -/
noncomputable abbrev specMapAlgebra (k : Type u) [Field k] (k' : Type u) [Field k']
    [Algebra k k'] : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k k'))

/-- **Restriction of tests along `k ⊆ k'`**: a `k'`-scheme `T` is in particular
a `k`-scheme, via `T ⟶ Spec k' ⟶ Spec k`. This is the functor along which the
descent step compares the two Picard functors. -/
noncomputable abbrev restrictTest (k : Type u) [Field k] (k' : Type u) [Field k']
    [Algebra k k'] : Over (Spec (CommRingCat.of k')) ⥤ Over (Spec (CommRingCat.of k)) :=
  Over.map (specMapAlgebra k k')

/-- `restrictTest` acts as the identity on the underlying scheme of a test. -/
@[simp]
theorem restrictTest_obj_left (T : Over (Spec (CommRingCat.of k'))) :
    ((restrictTest k k').obj T).left = T.left := rfl

/-- `restrictTest` composes the structure morphism with `φ`, by definition. -/
@[simp]
theorem restrictTest_obj_hom (T : Over (Spec (CommRingCat.of k'))) :
    ((restrictTest k k').obj T).hom = T.hom ≫ specMapAlgebra k k' := rfl

/-- The base change `T ×_k Spec k'` of a `k`-test `T`, regarded as a `k'`-test
via the second projection.

This is the object the descent step's classes live on: a class over `k'` is a
class on `T_{k'}` for the tests `T` of interest, and `§2` shows a `k`-class is
determined by its restriction here. -/
noncomputable abbrev baseTest (T : Over (Spec (CommRingCat.of k))) :
    Over (Spec (CommRingCat.of k')) :=
  Over.mk (pullback.snd T.hom (specMapAlgebra k k'))

/-- **The covering morphism `T_{k'} ⟶ T`**, in the slice over `Spec k`.

Its underlying scheme map is exactly `pullback.fst`, which is the morphism
`Picard/EtaleFieldCover.lean` builds its covering sieve from — so the sheaf
axiom landed there applies to this morphism on the nose (checked by `rfl`:
`coverMap_left`). -/
noncomputable def coverMap (T : Over (Spec (CommRingCat.of k))) :
    (restrictTest k k').obj (baseTest (k' := k') T) ⟶ T :=
  Over.homMk (pullback.fst T.hom (specMapAlgebra k k'))
    (pullback.condition (f := T.hom) (g := specMapAlgebra k k'))

/-- The cover morphism's underlying scheme map **is** `pullback.fst`, definitionally.

This is the identification that lets `§2` feed
`Scheme.picEt_ext_of_pullback_agrees`, whose sieve is generated by
`Presieve.singleton (pullback.fst T.hom (specMapAlgebra k k'))`. -/
@[simp]
theorem coverMap_left (T : Over (Spec (CommRingCat.of k))) :
    (coverMap (k' := k') T).left = pullback.fst T.hom (specMapAlgebra k k') := rfl

/-- `Spec γ : Spec k' ⟶ Spec k'`, the scheme map of a `k`-automorphism of `k'`. -/
noncomputable abbrev specGal (γ : k' ≃ₐ[k] k') :
    Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of k') :=
  Spec.map (CommRingCat.ofHom (γ : k' →+* k'))

/-- **`Spec γ` is a morphism over `Spec k`.**

This is `γ.commutes` — that `γ` fixes `k` — transported through `Spec`. It is the
only place the `k`-algebra structure of `γ` (as opposed to its being a ring
automorphism) is consumed, and everything else in this file is formal. -/
theorem specGal_comp (γ : k' ≃ₐ[k] k') :
    specGal γ ≫ specMapAlgebra k k' = specMapAlgebra k k' := by
  rw [specMapAlgebra, ← Spec.map_comp]
  congr 1
  ext x
  exact γ.commutes x

/-- The `γ`-twist of `T ×_k Spec k'` on underlying schemes: the identity on the `T`
factor and `Spec γ` on the `Spec k'` factor.

Well defined because `Spec γ` is a morphism over `Spec k` (`specGal_comp`), so the
twisted pair still satisfies the pullback condition. -/
noncomputable def twistLeft (T : Over (Spec (CommRingCat.of k))) (γ : k' ≃ₐ[k] k') :
    pullback T.hom (specMapAlgebra k k') ⟶ pullback T.hom (specMapAlgebra k k') :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ specGal γ) (by
    rw [Category.assoc, specGal_comp]
    exact pullback.condition)

/-- **The `γ`-twist as an endomorphism of the base-changed test, in the slice over
`Spec k`.**

This is the morphism a `γ`-invariance hypothesis is a statement about. **The
scheme-level twist already existed and an earlier revision of this docstring denied
it** (`I-1455`): `twistLeft` is `rfl`-equal to
`AlgebraicJacobian.GaloisDescent.pullbackGalMap k k' T.hom γ⁻¹`
(`Picard/FiniteGaloisQuotient.lean`, which also has the two projection identities
and the whole semilinear action). The denial was a census scoped to
`Picard/GaloisDescent/` reported as a fact about the project — literally true of the
directory, false of the tree, and exactly the trap that makes a lane rebuild a
landed construction. What this file adds is the **slice-over-`Spec k`** packaging,
which is what `picEt` consumes.

It is a slice morphism over `Spec k`, not over `Spec k'`: the twist moves the
`k'`-structure and is *not* `k'`-linear, which is exactly the semilinearity of the
Galois action, and is why the descent runs in the `k`-slice. -/
noncomputable def twistTest (T : Over (Spec (CommRingCat.of k))) (γ : k' ≃ₐ[k] k') :
    (restrictTest k k').obj (baseTest (k' := k') T) ⟶
      (restrictTest k k').obj (baseTest (k' := k') T) :=
  Over.homMk (twistLeft T γ) (by
    change twistLeft T γ ≫ pullback.snd _ _ ≫ specMapAlgebra k k' = _
    rw [twistLeft, pullback.lift_snd_assoc, Category.assoc, specGal_comp]
    rfl)

/-- **The twist lives over `T`**: it commutes with the covering morphism.

This is what makes the twist a morphism of *descent data* rather than merely of
schemes, and it is `pullback.lift_fst` — the twist is the identity on the `T`
factor. -/
theorem twistTest_comp_coverMap (T : Over (Spec (CommRingCat.of k))) (γ : k' ≃ₐ[k] k') :
    twistTest T γ ≫ coverMap (k' := k') T = coverMap (k' := k') T := by
  apply Over.OverMorphism.ext
  change twistLeft T γ ≫ pullback.fst _ _ = pullback.fst _ _
  exact pullback.lift_fst _ _ _

/-! ## §2. The `γ`-component section of the cover's self-pullback -/

/-- **THE COHERENCE, as a morphism**: the `γ`-component
`T_{k'} ⟶ T_{k'} ×_T T_{k'}`, namely `⟨𝟙, twist γ⟩`.

`PicEtDescentExistence.lean` §4 named the open link as "the `Gal`-coproduct's
`γ`-component inclusion composed with the two projections gives `id` and `γ`", with
the ingredients listed as `pullbackSpecIso`, `IsIso (sigmaSpec …)` and
`galoisSelfTensorEquiv`. **None of those three is needed for the coherence itself.**
The section exists by the universal property of the pullback, from
`twistTest_comp_coverMap` alone, and the two identities below are
`pullback.lift_fst` and `pullback.lift_snd`. The splitting is needed for something
else — see §4.

No hypothesis on `k'/k` beyond `[Algebra k k']`. -/
noncomputable def coverSelfSection (T : Over (Spec (CommRingCat.of k))) (γ : k' ≃ₐ[k] k') :
    (restrictTest k k').obj (baseTest (k' := k') T) ⟶
      pullback (coverMap (k := k) (k' := k') T) (coverMap (k := k) (k' := k') T) :=
  pullback.lift (𝟙 _) (twistTest T γ) (by
    rw [Category.id_comp, twistTest_comp_coverMap])

/-- The `γ`-component composed with the **first** projection is the identity. -/
@[simp] theorem coverSelfSection_fst (T : Over (Spec (CommRingCat.of k))) (γ : k' ≃ₐ[k] k') :
    coverSelfSection T γ ≫ pullback.fst (coverMap (k := k) (k' := k') T)
      (coverMap (k := k) (k' := k') T) = 𝟙 _ :=
  pullback.lift_fst _ _ _

/-- The `γ`-component composed with the **second** projection is the `γ`-twist. -/
@[simp] theorem coverSelfSection_snd (T : Over (Spec (CommRingCat.of k))) (γ : k' ≃ₐ[k] k') :
    coverSelfSection T γ ≫ pullback.snd (coverMap (k := k) (k' := k') T)
      (coverMap (k := k) (k' := k') T) = twistTest T γ :=
  pullback.lift_snd _ _ _

/-- **`Spec (k' ⊗_k k')` IS the `Gal`-indexed coproduct of copies of `Spec k'`** —
the scheme-level form of `ajc-p1`'s splitting, and the first thing `hcov` needs.

`galoisSelfTensorEquiv` is an algebra statement; this is it read through `Spec`,
composed with `sigmaSpec` being an isomorphism at a *finite* index set. Both halves
are library: `RingEquiv.toCommRingCatIso` turns the splitting into a `CommRingCat`
iso (an earlier revision here hand-built that iso with four field proofs — it is one
mathlib call, and `PicEtDescentExistence.lean` §4's own ingredient list named
`IsIso (sigmaSpec …)`, which *is* needed for this, unlike for §2's coherence).

**`[IsGalois k k']` is load-bearing here and only here in this file.** By
`galoisSelfTensorHom_bijective_iff_isGalois` the splitting is *false* at a merely
finite separable level, so this iso does not exist there — which is the precise
sense in which `hcov` fails rather than being unproved below the Galois level.

**What this does NOT yet give**, stated so the gap is not read as closed: `hcov` is
about the self-pullback of `coverMap` over an arbitrary test `T`, i.e. this object
*base-changed along* `T_{k'} ⟶ Spec k'`, and it needs the coproduct's `γ`-component
to be identified with `coverSelfSection T γ`. This iso is the input to that
identification, not the identification. -/
noncomputable def selfTensorSpecCoproduct (k k' : Type u) [Field k] [Field k']
    [Algebra k k'] [FiniteDimensional k k'] [IsGalois k k'] :
    (∐ fun _ : (k' ≃ₐ[k] k') => Spec (CommRingCat.of k')) ≅
      Spec (CommRingCat.of (k' ⊗[k] k')) :=
  (asIso (AlgebraicGeometry.sigmaSpec (fun _ : (k' ≃ₐ[k] k') => CommRingCat.of k'))) ≪≫
    Scheme.Spec.mapIso
      ((RingEquiv.toCommRingCatIso
        (AlgebraicJacobian.GaloisDescent.galoisSelfTensorEquiv k k').toRingEquiv).op)

theorem galoisSelfTensor_includeLeft (k' : Type u) [Field k'] [Algebra k k']
    [FiniteDimensional k k'] [IsGalois k k'] (γ : k' ≃ₐ[k] k') (a : k') :
    AlgebraicJacobian.GaloisDescent.galoisSelfTensorEquiv k k'
      (Algebra.TensorProduct.includeLeftRingHom a) γ = a := by
  change AlgebraicJacobian.GaloisDescent.galoisSelfTensorEquiv k k'
    (a ⊗ₜ[k] (1 : k')) γ = a
  simp [AlgebraicJacobian.GaloisDescent.galoisSelfTensorEquiv_apply_tmul]

theorem galoisSelfTensor_includeRight (k' : Type u) [Field k'] [Algebra k k']
    [FiniteDimensional k k'] [IsGalois k k'] (γ : k' ≃ₐ[k] k') (a : k') :
    AlgebraicJacobian.GaloisDescent.galoisSelfTensorEquiv k k'
      ((1 : k') ⊗ₜ[k] a) γ = γ a := by
  simp [AlgebraicJacobian.GaloisDescent.galoisSelfTensorEquiv_apply_tmul]


section EtaleSections

variable [Algebra.IsSeparable k k'] [Module.Finite k k']

/-- **The `γ`-section is `Etale`, and it needs no open-immersion input.**

`coverSelfSection T γ` is a *section* of `pullback.fst (coverMap T) (coverMap T)`
by `coverSelfSection_fst`, and that projection is `Etale` on underlying schemes
as a base change of `(coverMap T).left`. `Etale` has
`MorphismProperty.HasOfPostcompProperty @Etale`, so cancelling the projection
off the identity gives the section's own étaleness.

Arbitrary `γ`, arbitrary test `T`, no `[IsGalois k k']`: this is where the
previously-quoted "genuinely owed" half of `hcov` goes. -/
theorem etale_coverSelfSection_left (T : Over (Spec (CommRingCat.of k)))
    (γ : k' ≃ₐ[k] k') :
    Etale (coverSelfSection (k := k) (k' := k') T γ).left := by
  have hcm : Etale (coverMap (k := k) (k' := k') T).left := by
    rw [coverMap_left]; exact etale_pullback_fst_specMap k k' T.left T.hom
  have hpb := (IsPullback.of_hasPullback (coverMap (k := k) (k' := k') T)
    (coverMap (k := k) (k' := k') T)).map (Over.forget (Spec (CommRingCat.of k)))
  have hfst : Etale (Limits.pullback.fst (coverMap (k := k) (k' := k') T)
      (coverMap (k := k) (k' := k') T)).left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Etale) hpb.flip hcm
  have hcomp : (coverSelfSection (k := k) (k' := k') T γ).left ≫
      (Limits.pullback.fst (coverMap (k := k) (k' := k') T)
        (coverMap (k := k) (k' := k') T)).left = 𝟙 _ := by
    rw [← Over.comp_left, coverSelfSection_fst]; rfl
  refine MorphismProperty.of_postcomp (W := @Etale) (W' := @Etale) _ _ hfst ?_
  rw [hcomp]; infer_instance

omit [Algebra.IsSeparable k k'] [Module.Finite k k'] in
/-- The `γ`-section is a monomorphism: it is split by `pullback.fst`.

Neither separability nor finiteness is consumed — being split is formal — so both
are `omit`ted; they are the étale half's price, not this one's. -/
theorem mono_coverSelfSection_left (T : Over (Spec (CommRingCat.of k)))
    (γ : k' ≃ₐ[k] k') :
    Mono (coverSelfSection (k := k) (k' := k') T γ).left := by
  have hfac : (coverSelfSection (k := k) (k' := k') T γ).left ≫
      (Limits.pullback.fst (coverMap (k := k) (k' := k') T)
        (coverMap (k := k) (k' := k') T)).left = 𝟙 _ := by
    rw [← Over.comp_left, coverSelfSection_fst]; rfl
  exact mono_of_mono_fac hfac

/-- **The withdrawn prescription's property, DERIVED from the étale one.**

`IsOpenImmersion (coverSelfSection T γ).left` — the thing `I-1458` and two
docstrings called the "genuinely owed" half of `hcov` — follows in three lines
from `etale_coverSelfSection_left`: `Etale` gives `Flat` and
`LocallyOfFinitePresentation` by synthesis, `mono_coverSelfSection_left` gives
`Mono`, and `IsOpenImmersion.of_flat_of_mono` finishes.

**This declaration exists to make the correction compiler-checked rather than
asserted.** It is *why* calling `IsOpenImmersion` "strictly stronger" was wrong
(`I-1510`): at this site the two are equivalent, and the expensive one is a
corollary of the cheap one. Note that `hcov_of_jointlySurjective` does not use
it — the site never needed it — which is the separate point. -/
theorem isOpenImmersion_coverSelfSection_left (T : Over (Spec (CommRingCat.of k)))
    (γ : k' ≃ₐ[k] k') :
    IsOpenImmersion (coverSelfSection (k := k) (k' := k') T γ).left :=
  haveI := etale_coverSelfSection_left (k := k) (k' := k') T γ
  haveI := mono_coverSelfSection_left (k := k) (k' := k') T γ
  IsOpenImmersion.of_flat_of_mono _

end EtaleSections


end PicScheme

end Scheme

end AlgebraicGeometry

namespace AlgebraicJacobian.GaloisDescent

open scoped TensorProduct
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.PicScheme

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']
  [FiniteDimensional k k'] [IsGalois k k']

noncomputable def fieldSelfSection (γ : k' ≃ₐ[k] k') :
    Spec (CommRingCat.of k') ⟶
      pullback (specMapAlgebra k k') (specMapAlgebra k k') :=
  Limits.Sigma.ι (fun _ : k' ≃ₐ[k] k' => Spec (CommRingCat.of k')) γ ≫
    (selfTensorSpecCoproduct k k').hom ≫
    (AlgebraicGeometry.pullbackSpecIso k k' k').inv

@[simp, reassoc]
theorem fieldSelfSection_fst (γ : k' ≃ₐ[k] k') :
    fieldSelfSection (k := k) (k' := k') γ ≫
      pullback.fst (specMapAlgebra k k') (specMapAlgebra k k') = 𝟙 _ := by
  unfold fieldSelfSection
  rw [Category.assoc, Category.assoc,
    AlgebraicGeometry.pullbackSpecIso_inv_fst]
  unfold selfTensorSpecCoproduct
  simp only [Iso.trans_hom, asIso_hom, Category.assoc]
  rw [AlgebraicGeometry.ι_sigmaSpec_assoc]
  simp only [Functor.mapIso_hom, Iso.op_hom, Scheme.Spec_map,
    Quiver.Hom.unop_op]
  rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext x
  exact AlgebraicGeometry.Scheme.PicScheme.galoisSelfTensor_includeLeft k' γ x

@[simp, reassoc]
theorem fieldSelfSection_snd (γ : k' ≃ₐ[k] k') :
    fieldSelfSection (k := k) (k' := k') γ ≫
      pullback.snd (specMapAlgebra k k') (specMapAlgebra k k') = specGal γ := by
  unfold fieldSelfSection
  rw [Category.assoc, Category.assoc,
    AlgebraicGeometry.pullbackSpecIso_inv_snd]
  unfold selfTensorSpecCoproduct
  simp only [Iso.trans_hom, asIso_hom, Category.assoc]
  rw [AlgebraicGeometry.ι_sigmaSpec_assoc]
  simp only [Functor.mapIso_hom, Iso.op_hom, Scheme.Spec_map,
    Quiver.Hom.unop_op]
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext x
  exact AlgebraicGeometry.Scheme.PicScheme.galoisSelfTensor_includeRight k' γ x

instance fieldSelfSection_isOpenImmersion (γ : k' ≃ₐ[k] k') :
    IsOpenImmersion (fieldSelfSection (k := k) (k' := k') γ) := by
  haveI : IsOpenImmersion
      (Limits.Sigma.ι (fun _ : k' ≃ₐ[k] k' => Spec (CommRingCat.of k')) γ) :=
    (AlgebraicGeometry.sigmaOpenCover
      (fun _ : k' ≃ₐ[k] k' => Spec (CommRingCat.of k'))).map_prop γ
  unfold fieldSelfSection
  infer_instance

theorem fieldSelfSection_jointlySurjective :
    ∀ x : (Limits.pullback (specMapAlgebra k k')
      (specMapAlgebra k k') : Scheme.{u}),
      ∃ (γ : k' ≃ₐ[k] k') (y : Spec (CommRingCat.of k')),
        fieldSelfSection (k := k) (k' := k') γ y = x := by
  intro x
  let e := selfTensorSpecCoproduct k k' ≪≫
    (AlgebraicGeometry.pullbackSpecIso k k' k').symm
  obtain ⟨⟨γ, y⟩, hy⟩ := (AlgebraicGeometry.sigmaMk
    (fun _ : k' ≃ₐ[k] k' => Spec (CommRingCat.of k'))).surjective (e.inv x)
  rw [AlgebraicGeometry.sigmaMk_mk] at hy
  refine ⟨γ, y, ?_⟩
  change e.hom ((Limits.Sigma.ι
    (fun _ : k' ≃ₐ[k] k' => Spec (CommRingCat.of k')) γ) y) = x
  rw [hy]
  exact (Scheme.homeoOfIso e).apply_symm_apply x

noncomputable def fieldSelfOpenCover :
    Scheme.OpenCover (pullback (specMapAlgebra k k') (specMapAlgebra k k')) :=
  Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) (k' ≃ₐ[k] k')
    (fun _ => Spec (CommRingCat.of k'))
    (fun γ => fieldSelfSection (k := k) (k' := k') γ)
    (fieldSelfSection_jointlySurjective (k := k) (k' := k'))
    (fun γ => fieldSelfSection_isOpenImmersion (k := k) (k' := k') γ)

@[simp]
theorem fieldSelfOpenCover_f (γ : k' ≃ₐ[k] k') :
    (fieldSelfOpenCover (k := k) (k' := k')).f γ =
      fieldSelfSection (k := k) (k' := k') γ := rfl

noncomputable def relativeFieldSelfSection
    (T : Over (Spec (CommRingCat.of k))) (γ : k' ≃ₐ[k] k') :
    pullback T.hom (specMapAlgebra k k') ⟶
      pullback (pullback.snd T.hom (specMapAlgebra k k'))
        (pullback.fst (specMapAlgebra k k') (specMapAlgebra k k')) :=
  pullback.lift (𝟙 _)
    (pullback.snd T.hom (specMapAlgebra k k') ≫
      fieldSelfSection (k := k) (k' := k') γ)
    (by simp)

noncomputable def relativeFieldSelfOpenCover
    (T : Over (Spec (CommRingCat.of k))) :
    Scheme.OpenCover
      (pullback (pullback.snd T.hom (specMapAlgebra k k'))
        (pullback.fst (specMapAlgebra k k') (specMapAlgebra k k'))) :=
  Scheme.Pullback.openCoverOfRight (fieldSelfOpenCover (k := k) (k' := k'))
    (pullback.snd T.hom (specMapAlgebra k k'))
    (pullback.fst (specMapAlgebra k k') (specMapAlgebra k k'))

set_option backward.isDefEq.respectTransparency false in
theorem relativeFieldSelfOpenCover_factors
    (T : Over (Spec (CommRingCat.of k))) (γ : k' ≃ₐ[k] k') :
    (relativeFieldSelfOpenCover (k := k) (k' := k') T).f γ =
      pullback.fst (pullback.snd T.hom (specMapAlgebra k k'))
          (fieldSelfSection (k := k) (k' := k') γ ≫
            pullback.fst (specMapAlgebra k k') (specMapAlgebra k k')) ≫
      relativeFieldSelfSection (k := k) (k' := k') T γ := by
  change (Scheme.Pullback.openCoverOfRight
    (fieldSelfOpenCover (k := k) (k' := k'))
    (pullback.snd T.hom (specMapAlgebra k k'))
    (pullback.fst (specMapAlgebra k k') (specMapAlgebra k k'))).f γ = _
  rw [Scheme.Pullback.openCoverOfRight_f]
  simp only [fieldSelfOpenCover_f]
  apply pullback.hom_ext
  · simp only [pullback.map, relativeFieldSelfSection, pullback.lift_fst]
    rw [Category.comp_id, Category.assoc, pullback.lift_fst]
    simp
  · simp only [pullback.map, relativeFieldSelfSection, pullback.lift_snd]
    rw [Category.assoc, pullback.lift_snd]
    simp only [← Category.assoc]
    rw [pullback.condition]
    simp

theorem relativeFieldSelfSection_jointlySurjective
    (T : Over (Spec (CommRingCat.of k))) :
    ∀ x : (Limits.pullback (pullback.snd T.hom (specMapAlgebra k k'))
        (pullback.fst (specMapAlgebra k k') (specMapAlgebra k k')) : Scheme.{u}),
      ∃ (γ : k' ≃ₐ[k] k')
        (y : (Limits.pullback T.hom (specMapAlgebra k k') : Scheme.{u})),
        relativeFieldSelfSection (k := k) (k' := k') T γ y = x := by
  intro x
  obtain ⟨γ, z, hz⟩ :=
    (relativeFieldSelfOpenCover (k := k) (k' := k') T).exists_eq x
  refine ⟨γ,
    pullback.fst (pullback.snd T.hom (specMapAlgebra k k'))
      (fieldSelfSection (k := k) (k' := k') γ ≫
        pullback.fst (specMapAlgebra k k') (specMapAlgebra k k')) z, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← relativeFieldSelfOpenCover_factors]
  exact hz

omit [FiniteDimensional k k'] [IsGalois k k'] in
theorem forget_coverMap_eq_pullbackFst
    (T : Over (Spec (CommRingCat.of k))) :
    (Over.forget (Spec (CommRingCat.of k))).map
        (coverMap (k := k) (k' := k') T) =
      pullback.fst T.hom (specMapAlgebra k k') := rfl

noncomputable def coverSelfRelativeFieldIsoUnderlying
    (T : Over (Spec (CommRingCat.of k))) :
    (Over.forget (Spec (CommRingCat.of k))).obj
        (pullback (coverMap (k := k) (k' := k') T)
          (coverMap (k := k) (k' := k') T)) ≅
      pullback (pullback.snd T.hom (specMapAlgebra k k'))
        (pullback.fst (specMapAlgebra k k') (specMapAlgebra k k')) :=
  (PreservesPullback.iso (Over.forget (Spec (CommRingCat.of k)))
      (coverMap (k := k) (k' := k') T)
      (coverMap (k := k) (k' := k') T)) ≪≫
    pullback.congrHom (forget_coverMap_eq_pullbackFst (k := k) (k' := k') T)
      (forget_coverMap_eq_pullbackFst (k := k) (k' := k') T) ≪≫
    pullbackRightPullbackFstIso T.hom (specMapAlgebra k k')
      (pullback.fst T.hom (specMapAlgebra k k')) ≪≫
    ((pullbackRightPullbackFstIso (specMapAlgebra k k')
        (specMapAlgebra k k')
        (pullback.snd T.hom (specMapAlgebra k k'))) ≪≫
      pullback.congrHom pullback.condition.symm rfl).symm

noncomputable def coverSelfRelativeFieldIso
    (T : Over (Spec (CommRingCat.of k))) :
    (pullback (coverMap (k := k) (k' := k') T)
      (coverMap (k := k) (k' := k') T)).left ≅
      pullback (pullback.snd T.hom (specMapAlgebra k k'))
        (pullback.fst (specMapAlgebra k k') (specMapAlgebra k k')) :=
  coverSelfRelativeFieldIsoUnderlying (k := k) (k' := k') T

omit [FiniteDimensional k k'] [IsGalois k k'] in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem coverSelfRelativeFieldIso_hom_fst
    (T : Over (Spec (CommRingCat.of k))) :
    (coverSelfRelativeFieldIso (k := k) (k' := k') T).hom ≫
        pullback.fst (pullback.snd T.hom (specMapAlgebra k k'))
          (pullback.fst (specMapAlgebra k k') (specMapAlgebra k k')) =
      (pullback.fst (coverMap (k := k) (k' := k') T)
        (coverMap (k := k) (k' := k') T)).left := by
  change (coverSelfRelativeFieldIsoUnderlying (k := k) (k' := k') T).hom ≫ _ =
    (Over.forget (Spec (CommRingCat.of k))).map
      (pullback.fst (coverMap (k := k) (k' := k') T)
        (coverMap (k := k) (k' := k') T))
  simp only [coverSelfRelativeFieldIsoUnderlying,
    Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Category.assoc,
    pullbackRightPullbackFstIso_inv_fst,
    pullback.congrHom_inv, pullback.congrHom_hom,
    pullback.lift_fst, Category.comp_id,
    pullbackRightPullbackFstIso_hom_fst,
    PreservesPullback.iso_hom_fst]

omit [FiniteDimensional k k'] [IsGalois k k'] in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem coverSelfRelativeFieldIso_hom_snd_fst
    (T : Over (Spec (CommRingCat.of k))) :
    (coverSelfRelativeFieldIso (k := k) (k' := k') T).hom ≫
          pullback.snd (pullback.snd T.hom (specMapAlgebra k k'))
            (pullback.fst (specMapAlgebra k k') (specMapAlgebra k k')) ≫
          pullback.fst (specMapAlgebra k k') (specMapAlgebra k k') =
      (pullback.fst (coverMap (k := k) (k' := k') T)
          (coverMap (k := k) (k' := k') T)).left ≫
        pullback.snd T.hom (specMapAlgebra k k') := by
  change (coverSelfRelativeFieldIsoUnderlying (k := k) (k' := k') T).hom ≫ _ ≫ _ =
    (Over.forget (Spec (CommRingCat.of k))).map
        (pullback.fst (coverMap (k := k) (k' := k') T)
          (coverMap (k := k) (k' := k') T)) ≫ _
  simp only [coverSelfRelativeFieldIsoUnderlying,
    Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Category.assoc,
    pullbackRightPullbackFstIso_inv_snd_fst,
    pullback.congrHom_inv, pullback.congrHom_hom,
    pullback.lift_fst_assoc, Category.comp_id,
    pullbackRightPullbackFstIso_hom_fst_assoc,
    PreservesPullback.iso_hom_fst_assoc]

omit [FiniteDimensional k k'] [IsGalois k k'] in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem coverSelfRelativeFieldIso_hom_snd_snd
    (T : Over (Spec (CommRingCat.of k))) :
    (coverSelfRelativeFieldIso (k := k) (k' := k') T).hom ≫
          pullback.snd (pullback.snd T.hom (specMapAlgebra k k'))
            (pullback.fst (specMapAlgebra k k') (specMapAlgebra k k')) ≫
          pullback.snd (specMapAlgebra k k') (specMapAlgebra k k') =
      (pullback.snd (coverMap (k := k) (k' := k') T)
          (coverMap (k := k) (k' := k') T)).left ≫
        pullback.snd T.hom (specMapAlgebra k k') := by
  change (coverSelfRelativeFieldIsoUnderlying (k := k) (k' := k') T).hom ≫ _ ≫ _ =
    (Over.forget (Spec (CommRingCat.of k))).map
        (pullback.snd (coverMap (k := k) (k' := k') T)
          (coverMap (k := k) (k' := k') T)) ≫ _
  simp only [coverSelfRelativeFieldIsoUnderlying,
    Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Category.assoc,
    pullbackRightPullbackFstIso_inv_snd_snd,
    pullback.congrHom_inv, pullback.congrHom_hom,
    pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id,
    pullbackRightPullbackFstIso_hom_snd,
    PreservesPullback.iso_hom_snd_assoc]

set_option backward.isDefEq.respectTransparency false in
theorem coverSelfSection_comp_coverSelfRelativeFieldIso
    (T : Over (Spec (CommRingCat.of k))) (γ : k' ≃ₐ[k] k') :
    (coverSelfSection (k := k) (k' := k') T γ).left ≫
        (coverSelfRelativeFieldIso (k := k) (k' := k') T).hom =
      relativeFieldSelfSection (k := k) (k' := k') T γ := by
  have hfst := congrArg Over.Hom.left
    (coverSelfSection_fst (k := k) (k' := k') T γ)
  have hsnd := congrArg Over.Hom.left
    (coverSelfSection_snd (k := k) (k' := k') T γ)
  simp only [Over.comp_left, Over.id_left] at hfst hsnd
  apply pullback.hom_ext
  · simp only [relativeFieldSelfSection, pullback.lift_fst]
    rw [Category.assoc, coverSelfRelativeFieldIso_hom_fst, hfst]
    change 𝟙 ((restrictTest k k').obj (baseTest (k' := k') T)).left =
      𝟙 ((restrictTest k k').obj (baseTest (k' := k') T)).left
    rfl
  · apply pullback.hom_ext
    · simp only [relativeFieldSelfSection, pullback.lift_snd,
        Category.assoc, fieldSelfSection_fst, Category.comp_id]
      have hproj := congrArg
        (fun z => (coverSelfSection (k := k) (k' := k') T γ).left ≫ z)
        (coverSelfRelativeFieldIso_hom_snd_fst (k := k) (k' := k') T)
      calc
        _ = ((coverSelfSection (k := k) (k' := k') T γ).left ≫
              (pullback.fst (coverMap (k := k) (k' := k') T)
                (coverMap (k := k) (k' := k') T)).left) ≫
            pullback.snd T.hom (specMapAlgebra k k') := by
          simpa only [Category.assoc] using hproj
        _ = 𝟙 ((restrictTest k k').obj (baseTest (k' := k') T)).left ≫
            pullback.snd T.hom (specMapAlgebra k k') :=
          congrArg (fun z => z ≫ pullback.snd T.hom (specMapAlgebra k k')) hfst
        _ = _ := Category.id_comp _
    · simp only [relativeFieldSelfSection, pullback.lift_snd,
        Category.assoc, fieldSelfSection_snd]
      have hproj := congrArg
        (fun z => (coverSelfSection (k := k) (k' := k') T γ).left ≫ z)
        (coverSelfRelativeFieldIso_hom_snd_snd (k := k) (k' := k') T)
      calc
        _ = ((coverSelfSection (k := k) (k' := k') T γ).left ≫
              (pullback.snd (coverMap (k := k) (k' := k') T)
                (coverMap (k := k) (k' := k') T)).left) ≫
            pullback.snd T.hom (specMapAlgebra k k') := by
          simpa only [Category.assoc] using hproj
        _ = (twistTest T γ).left ≫
            pullback.snd T.hom (specMapAlgebra k k') :=
          congrArg (fun z => z ≫ pullback.snd T.hom (specMapAlgebra k k')) hsnd
        _ = _ := by simp [twistTest, twistLeft]

theorem coverSelfSection_jointlySurjective
    (T : Over (Spec (CommRingCat.of k))) :
    ∀ x : (Limits.pullback (coverMap (k := k) (k' := k') T)
        (coverMap (k := k) (k' := k') T)).left,
      ∃ (γ : k' ≃ₐ[k] k')
        (y : ((restrictTest k k').obj (baseTest (k' := k') T)).left),
        (coverSelfSection (k := k) (k' := k') T γ).left y = x := by
  intro x
  obtain ⟨γ, y, hy⟩ := relativeFieldSelfSection_jointlySurjective
    (k := k) (k' := k') T
    ((coverSelfRelativeFieldIso (k := k) (k' := k') T).hom x)
  change ((restrictTest k k').obj (baseTest (k' := k') T)).left at y
  refine ⟨γ, y, ?_⟩
  apply (Scheme.homeoOfIso
    (coverSelfRelativeFieldIso (k := k) (k' := k') T)).injective
  have hp := congrArg
    (fun m : ((restrictTest k k').obj (baseTest (k' := k') T)).left ⟶ _ => m y)
    (coverSelfSection_comp_coverSelfRelativeFieldIso
      (k := k) (k' := k') T γ)
  rw [Scheme.Hom.comp_apply] at hp
  change (coverSelfRelativeFieldIso (k := k) (k' := k') T).hom
      ((coverSelfSection (k := k) (k' := k') T γ).left y) =
    (coverSelfRelativeFieldIso (k := k) (k' := k') T).hom x
  exact hp.trans hy

noncomputable def coverSelfSectionOpenCover
    (T : Over (Spec (CommRingCat.of k))) :
    Scheme.OpenCover
      (pullback (coverMap (k := k) (k' := k') T)
        (coverMap (k := k) (k' := k') T)).left :=
  Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) (k' ≃ₐ[k] k')
    (fun _ => ((restrictTest k k').obj (baseTest (k' := k') T)).left)
    (fun γ => (coverSelfSection (k := k) (k' := k') T γ).left)
    (coverSelfSection_jointlySurjective (k := k) (k' := k') T)
    (fun γ => isOpenImmersion_coverSelfSection_left T γ)

theorem coverSelfSection_hom_ext
    (T : Over (Spec (CommRingCat.of k))) {Z : Scheme.{u}}
    {a b : (pullback (coverMap (k := k) (k' := k') T)
      (coverMap (k := k) (k' := k') T)).left ⟶ Z}
    (h : ∀ γ : k' ≃ₐ[k] k',
      (coverSelfSection (k := k) (k' := k') T γ).left ≫ a =
        (coverSelfSection (k := k) (k' := k') T γ).left ≫ b) :
    a = b :=
  Scheme.Cover.hom_ext (coverSelfSectionOpenCover (k := k) (k' := k') T) a b h

end AlgebraicJacobian.GaloisDescent
