/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Picard.ProjectiveMorphismBasic
import AlgebraicJacobian.Picard.SerreTwist
import AlgebraicJacobian.Picard.QuotFunctorDef

/-!
# Projective and H-quasi-projective morphisms carrying a very ample line bundle

Mathlib v4.31 has no projective-morphism class and no (very) ampleness
vocabulary.  Following the encoding settled in inbox `I-0118` (comment
`C-0002`), this file defines:

* `ProjectiveSpace.twistingSheaf n₀ S m` — the Serre twist `O(m)` on the
  relative projective space `ℙ(n₀; S)`, the pullback of
  `ProjTwist.serreTwist` from the integral model along `toProjInt`;
* `ProjectiveSpace.twistingSheafBaseChange` — `O(m)` commutes with base
  change of the ambient projective space;
* `Scheme.Hom.IsProjectiveWith π L` — the **projective-with-`L`** predicate:
  `π : X ⟶ S` factors through a closed immersion `i : X ↪ ℙ(n; S)` for a
  finite coordinate type `n`, over `S` with `L ≅ i^* O(1)`;
* `Scheme.Hom.IsHQuasiProjectiveWith π L` — the corresponding
  **H-quasi-projective-with-`L`** predicate, with a quasi-compact immersion into
  finite projective space and the same `O(1)` comparison.

with the stability facts the Quot-scheme endgame consumes:

* `Scheme.Hom.IsProjectiveWith.isProper` — projective morphisms are proper;
* `Scheme.Hom.IsProjectiveWith.comp_isClosedImmersion` — a closed immersion
  into a projective scheme is projective (carrying the restricted bundle);
* `Scheme.Hom.IsProjectiveWith.baseChange` — stability under base change
  (carrying the pulled-back bundle).

The `IsHQuasiProjectiveWith` terminology records the finite-projective-space
convention.  No equivalence with every relative ample formulation over an
arbitrary base is asserted here.

The ampleness predicates and their carried-bundle stability theorems are at
`Scheme.{0}`: the Serre twist rests on the descent engine
`Scheme.Modules.glue`, which is universe-monomorphic at `Scheme.GlueData.{0}`
(`GlueDescent.lean:934`).  The purely scheme-theoretic open-image isomorphism is
universe-polymorphic.

Blueprint: `def:twisting_sheaf`, `def:projective_with`,
`lem:projective_with_proper`, `lem:projective_with_closed_immersion`,
`lem:projective_with_base_change`
(`blueprint/src/chapters/Picard_QuotScheme.tex`).
-/

open CategoryTheory Limits MvPolynomial

noncomputable section

namespace AlgebraicGeometry

namespace ProjectiveSpace

variable (n₀ : Type) (S : Scheme.{0})

/-- The Serre twist `O(m)` on the relative projective space `ℙ(n₀; S)`:
the pullback of the glued twisting sheaf on the integral model. -/
def twistingSheaf (m : ℕ) : (ℙ(n₀; S)).Modules :=
  (Scheme.Modules.pullback (toProjInt n₀ S)).obj (ProjTwist.serreTwist n₀ m)

variable {S} {S' : Scheme.{0}}

/-- The Serre twist commutes with base change of the ambient projective
space: `(map g)^* O(m) ≅ O(m)`. -/
def twistingSheafBaseChange (g : S' ⟶ S) (m : ℕ) :
    (Scheme.Modules.pullback (map n₀ g)).obj (twistingSheaf n₀ S m) ≅
      twistingSheaf n₀ S' m :=
  Scheme.pullbackTriangleIso (map_toProjInt n₀ g) (ProjTwist.serreTwist n₀ m)

end ProjectiveSpace

/-- `π : X ⟶ S` is a **projective morphism carrying the line bundle `L`**
([Nitsure] §5, [EGA II] 5.5): there are a finite coordinate type `n`, a closed
immersion `i : X ↪ ℙ(n; S)` over `S`, and an isomorphism of `L` with the
pullback of the Serre twist `O(1)`.  This is the faithful encoding of
"projective with relatively very ample `L`" settled in inbox `I-0118`. -/
def Scheme.Hom.IsProjectiveWith {X S : Scheme.{0}} (π : X ⟶ S) (L : X.Modules) :
    Prop :=
  ∃ (n : Type) (_ : Finite n) (i : X ⟶ ℙ(n; S)),
    IsClosedImmersion i ∧ i ≫ (ℙ(n; S) ↘ S) = π ∧
      Nonempty (L ≅ (Scheme.Modules.pullback i).obj
        (ProjectiveSpace.twistingSheaf n S 1))

/-- `π : X ⟶ S` is **H-quasi-projective carrying `L`** if it admits a
quasi-compact immersion into a finite-dimensional relative projective space,
over `S`, which identifies `L` with the pullback of `O(1)`.  This is the
project-local encoding of a specified relatively very ample line bundle. -/
def Scheme.Hom.IsHQuasiProjectiveWith {X S : Scheme.{0}} (π : X ⟶ S)
    (L : X.Modules) : Prop :=
  ∃ (n : Type) (_ : Finite n) (i : X ⟶ ℙ(n; S)),
    IsImmersion i ∧ QuasiCompact i ∧ i ≫ (ℙ(n; S) ↘ S) = π ∧
      Nonempty (L ≅ (Scheme.Modules.pullback i).obj
        (ProjectiveSpace.twistingSheaf n S 1))

namespace Scheme.Hom.IsProjective

variable {X S : Scheme.{0}} {π : X ⟶ S}

/-- Every projective morphism carries a relatively very ample line bundle: choose the
pullback of `O(1)` along the closed immersion in the `IsProjective` witness. -/
theorem exists_isProjectiveWith (h : π.IsProjective) :
    ∃ L : X.Modules, π.IsProjectiveWith L := by
  obtain ⟨n, hn, i, hi, hcomp⟩ := h
  letI : Finite n := hn
  let L := (Scheme.Modules.pullback i).obj
    (ProjectiveSpace.twistingSheaf n S 1)
  exact ⟨L, n, inferInstance, i, hi, hcomp, ⟨Iso.refl _⟩⟩

end Scheme.Hom.IsProjective

namespace Scheme.Hom.IsProjectiveWith

variable {X S : Scheme.{0}} {π : X ⟶ S} {L : X.Modules}

/-- Forget the chosen very ample line bundle from a projective morphism. -/
theorem isProjective (h : π.IsProjectiveWith L) : π.IsProjective := by
  obtain ⟨n, hn, i, hi, hcomp, -⟩ := h
  exact ⟨n, hn, i, hi, hcomp⟩

/-- A projective morphism carrying `L` is H-quasi-projective carrying the same
line bundle. -/
theorem isHQuasiProjectiveWith (h : π.IsProjectiveWith L) :
    π.IsHQuasiProjectiveWith L := by
  obtain ⟨n, hn, i, hi, hcomp, hL⟩ := h
  letI : Finite n := hn
  haveI : IsClosedImmersion i := hi
  exact ⟨n, hn, i, inferInstance, inferInstance, hcomp, hL⟩

/-- **Projective morphisms are proper**: a closed immersion is proper, the
structural morphism of projective space is proper, and properness is stable
under composition. -/
theorem isProper (h : π.IsProjectiveWith L) : IsProper π := by
  exact h.isProjective.isProper

/-- **Projective morphisms are locally of finite type**: immediate from
`isProper`, since properness extends `LocallyOfFiniteType`.  This lets the
Quot-scheme endgame and the Hilbert-polynomial existence theorem derive finite
type from projectivity instead of carrying it as a separate hypothesis. -/
theorem locallyOfFiniteType (h : π.IsProjectiveWith L) : LocallyOfFiniteType π :=
  haveI := h.isProper; inferInstance

/-- **Projective morphisms are separated** (properness extends `IsSeparated`). -/
theorem isSeparated (h : π.IsProjectiveWith L) : IsSeparated π :=
  haveI := h.isProper; inferInstance

/-- **Projective morphisms are universally closed** (properness extends
`UniversallyClosed`). -/
theorem universallyClosed (h : π.IsProjectiveWith L) : UniversallyClosed π :=
  haveI := h.isProper; inferInstance

/-- **Transfer along an isomorphism of the carried bundle**: `IsProjectiveWith`
depends on `L` only up to isomorphism (it records the comparison `L ≅ i^* O(1)`
through `Nonempty`), so if `π` is projective carrying `L` and `L ≅ L'`, then `π`
is projective carrying `L'`.  Useful for consumers that only have the bundle up
to isomorphism. -/
theorem of_iso (h : π.IsProjectiveWith L) {L' : X.Modules} (e : L ≅ L') :
    π.IsProjectiveWith L' := by
  obtain ⟨n, hn, i, hi, hcomp, ⟨eL⟩⟩ := h
  exact ⟨n, hn, i, hi, hcomp, ⟨e.symm ≪≫ eL⟩⟩

/-- **Composition with a closed immersion**: if `π` is projective carrying
`L` and `j` is a closed immersion into `X`, then `j ≫ π` is projective
carrying `j^* L`. -/
theorem comp_isClosedImmersion (h : π.IsProjectiveWith L) {Y : Scheme.{0}}
    (j : Y ⟶ X) [IsClosedImmersion j] :
    (j ≫ π).IsProjectiveWith ((Scheme.Modules.pullback j).obj L) := by
  obtain ⟨n, hn, i, hi, hcomp, ⟨e⟩⟩ := h
  letI : Finite n := hn
  haveI := hi
  refine ⟨n, inferInstance, j ≫ i, inferInstance, by rw [Category.assoc, hcomp], ?_⟩
  exact ⟨(Scheme.Modules.pullback j).mapIso e ≪≫
    Scheme.pullbackTriangleIso (rfl : j ≫ i = j ≫ i)
      (ProjectiveSpace.twistingSheaf n S 1)⟩

/-- The comparison morphism from the base-changed total space into the
base-changed projective space. -/
private def baseChangeLift {S' : Scheme.{0}} (g : S' ⟶ S) {n : Type} [Finite n]
    (i : X ⟶ ℙ(n; S)) (hcomp : i ≫ (ℙ(n; S) ↘ S) = π) :
    pullback π g ⟶ ℙ(n; S') :=
  (ProjectiveSpace.isPullback_map n g).lift
    (pullback.fst π g ≫ i) (pullback.snd π g)
    (by rw [Category.assoc, hcomp, pullback.condition])

/-- **Stability under base change**: if `π : X ⟶ S` is projective carrying
`L` and `g : S' ⟶ S`, then the base change `X ×_S S' ⟶ S'` is projective
carrying the pullback of `L`. -/
theorem baseChange (h : π.IsProjectiveWith L) {S' : Scheme.{0}} (g : S' ⟶ S) :
    (pullback.snd π g).IsProjectiveWith
      ((Scheme.Modules.pullback (pullback.fst π g)).obj L) := by
  obtain ⟨n, hn, i, hi, hcomp, ⟨e⟩⟩ := h
  letI : Finite n := hn
  haveI := hi
  refine ⟨n, inferInstance, baseChangeLift g i hcomp, ?_, ?_, ?_⟩
  · -- the comparison square exhibits the lift as the base change of `i`
    have h1 : baseChangeLift g i hcomp ≫ (ℙ(n; S') ↘ S')
        = pullback.snd π g := IsPullback.lift_snd _ _ _ _
    have hsq : IsPullback (baseChangeLift g i hcomp) (pullback.fst π g)
        (ProjectiveSpace.map n g) i := by
      have hbig : IsPullback
          (baseChangeLift g i hcomp ≫ (ℙ(n; S') ↘ S'))
          (pullback.fst π g) g (i ≫ (ℙ(n; S) ↘ S)) := by
        rw [h1, hcomp]
        exact (IsPullback.of_hasPullback π g).flip
      exact IsPullback.of_right hbig
        (IsPullback.lift_fst _ _ _ _)
        (ProjectiveSpace.isPullback_map n g).flip
    exact MorphismProperty.of_isPullback hsq.flip hi
  · exact IsPullback.lift_snd _ _ _ _
  · refine ⟨(Scheme.Modules.pullback (pullback.fst π g)).mapIso e ≪≫
      Scheme.pullbackTriangleIso (IsPullback.lift_fst _ _ _ _ :
        baseChangeLift g i hcomp ≫ ProjectiveSpace.map n g
          = pullback.fst π g ≫ i).symm
        (ProjectiveSpace.twistingSheaf n S 1) ≪≫ ?_⟩
    -- collapse `(lift ≫ map)^* O(1)` to `lift^* (map^* O(1))`, then use the
    -- base-change isomorphism of the twist
    exact (Scheme.pullbackTriangleIso
        (rfl : baseChangeLift g i hcomp ≫ ProjectiveSpace.map n g
          = _) (ProjectiveSpace.twistingSheaf n S 1)).symm ≪≫
      (Scheme.Modules.pullback (baseChangeLift g i hcomp)).mapIso
        (ProjectiveSpace.twistingSheafBaseChange n g 1)

end Scheme.Hom.IsProjectiveWith

namespace Scheme.Hom.IsHQuasiProjective

variable {X S : Scheme.{0}} {π : X ⟶ S}

/-- Every H-quasi-projective morphism carries a specified relatively very ample
line bundle: pull back `O(1)` along its immersion witness. -/
theorem exists_isHQuasiProjectiveWith (h : π.IsHQuasiProjective) :
    ∃ L : X.Modules, π.IsHQuasiProjectiveWith L := by
  obtain ⟨n, hn, i, hi, hqc, hcomp⟩ := h
  letI : Finite n := hn
  let L := (Scheme.Modules.pullback i).obj
    (ProjectiveSpace.twistingSheaf n S 1)
  exact ⟨L, n, inferInstance, i, hi, hqc, hcomp, ⟨Iso.refl _⟩⟩

end Scheme.Hom.IsHQuasiProjective

namespace Scheme.Hom.IsHQuasiProjectiveWith

variable {X S : Scheme.{0}} {π : X ⟶ S} {L : X.Modules}

/-- Forget the chosen relatively very ample line bundle. -/
theorem isHQuasiProjective (h : π.IsHQuasiProjectiveWith L) :
    π.IsHQuasiProjective := by
  obtain ⟨n, hn, i, hi, hqc, hcomp, -⟩ := h
  exact ⟨n, hn, i, hi, hqc, hcomp⟩

/-- H-quasi-projective morphisms carrying a line bundle are locally of finite type. -/
theorem locallyOfFiniteType (h : π.IsHQuasiProjectiveWith L) :
    LocallyOfFiniteType π :=
  h.isHQuasiProjective.locallyOfFiniteType

/-- H-quasi-projective morphisms carrying a line bundle are quasi-compact. -/
theorem quasiCompact (h : π.IsHQuasiProjectiveWith L) : QuasiCompact π :=
  h.isHQuasiProjective.quasiCompact

/-- H-quasi-projective morphisms carrying a line bundle are separated. -/
theorem isSeparated (h : π.IsHQuasiProjectiveWith L) : IsSeparated π :=
  h.isHQuasiProjective.isSeparated

/-- Transfer the carried H-quasi-projective structure along an isomorphism of
line bundles. -/
theorem of_iso (h : π.IsHQuasiProjectiveWith L) {L' : X.Modules} (e : L ≅ L') :
    π.IsHQuasiProjectiveWith L' := by
  obtain ⟨n, hn, i, hi, hqc, hcomp, ⟨eL⟩⟩ := h
  exact ⟨n, hn, i, hi, hqc, hcomp, ⟨e.symm ≪≫ eL⟩⟩

/-- Composition with a quasi-compact immersion preserves the carried
H-quasi-projective structure. -/
theorem comp_isImmersion (h : π.IsHQuasiProjectiveWith L) {Y : Scheme.{0}}
    (j : Y ⟶ X) [IsImmersion j] [QuasiCompact j] :
    (j ≫ π).IsHQuasiProjectiveWith ((Scheme.Modules.pullback j).obj L) := by
  obtain ⟨n, hn, i, hi, hqc, hcomp, ⟨e⟩⟩ := h
  letI : Finite n := hn
  haveI : IsImmersion i := hi
  haveI : QuasiCompact i := hqc
  refine ⟨n, inferInstance, j ≫ i, inferInstance, inferInstance,
    by rw [Category.assoc, hcomp], ?_⟩
  exact ⟨(Scheme.Modules.pullback j).mapIso e ≪≫
    Scheme.pullbackTriangleIso (rfl : j ≫ i = j ≫ i)
      (ProjectiveSpace.twistingSheaf n S 1)⟩

/-- Transport H-quasi-projectivity and its specified relatively very ample line
bundle along an isomorphism in `Over S`. -/
theorem of_over_iso {S₀ : Scheme.{0}} {X₀ Y₀ : Over S₀}
    {L₀ : X₀.left.Modules} (h : X₀.hom.IsHQuasiProjectiveWith L₀)
    (e : Y₀ ≅ X₀) :
    Y₀.hom.IsHQuasiProjectiveWith
      ((Scheme.Modules.pullback e.hom.left).obj L₀) := by
  rw [← Over.w e.hom]
  exact h.comp_isImmersion e.hom.left

/-- The comparison morphism from the base-changed total space into the
base-changed projective space. -/
private def baseChangeLift {S' : Scheme.{0}} (g : S' ⟶ S) {n : Type} [Finite n]
    (i : X ⟶ ℙ(n; S)) (hcomp : i ≫ (ℙ(n; S) ↘ S) = π) :
    pullback π g ⟶ ℙ(n; S') :=
  (ProjectiveSpace.isPullback_map n g).lift
    (pullback.fst π g ≫ i) (pullback.snd π g)
    (by rw [Category.assoc, hcomp, pullback.condition])

/-- H-quasi-projectivity with a specified relatively very ample line bundle is
stable under arbitrary base change. -/
theorem baseChange (h : π.IsHQuasiProjectiveWith L) {S' : Scheme.{0}} (g : S' ⟶ S) :
    (pullback.snd π g).IsHQuasiProjectiveWith
      ((Scheme.Modules.pullback (pullback.fst π g)).obj L) := by
  obtain ⟨n, hn, i, hi, hqc, hcomp, ⟨e⟩⟩ := h
  letI : Finite n := hn
  haveI : IsImmersion i := hi
  haveI : QuasiCompact i := hqc
  have h1 : baseChangeLift g i hcomp ≫ (ℙ(n; S') ↘ S') =
      pullback.snd π g := IsPullback.lift_snd _ _ _ _
  have hsq : IsPullback (baseChangeLift g i hcomp) (pullback.fst π g)
      (ProjectiveSpace.map n g) i := by
    have hbig : IsPullback
        (baseChangeLift g i hcomp ≫ (ℙ(n; S') ↘ S'))
        (pullback.fst π g) g (i ≫ (ℙ(n; S) ↘ S)) := by
      rw [h1, hcomp]
      exact (IsPullback.of_hasPullback π g).flip
    exact IsPullback.of_right hbig
      (IsPullback.lift_fst _ _ _ _)
      (ProjectiveSpace.isPullback_map n g).flip
  refine ⟨n, inferInstance, baseChangeLift g i hcomp,
    MorphismProperty.of_isPullback hsq.flip hi,
    MorphismProperty.of_isPullback hsq.flip hqc, h1, ?_⟩
  refine ⟨(Scheme.Modules.pullback (pullback.fst π g)).mapIso e ≪≫
    Scheme.pullbackTriangleIso (IsPullback.lift_fst _ _ _ _ :
      baseChangeLift g i hcomp ≫ ProjectiveSpace.map n g
        = pullback.fst π g ≫ i).symm
      (ProjectiveSpace.twistingSheaf n S 1) ≪≫ ?_⟩
  exact (Scheme.pullbackTriangleIso
      (rfl : baseChangeLift g i hcomp ≫ ProjectiveSpace.map n g = _)
      (ProjectiveSpace.twistingSheaf n S 1)).symm ≪≫
    (Scheme.Modules.pullback (baseChangeLift g i hcomp)).mapIso
      (ProjectiveSpace.twistingSheafBaseChange n g 1)

end Scheme.Hom.IsHQuasiProjectiveWith

/-- An isomorphism over `S` restricts to an isomorphism over `S` from an open
subscheme to its open image. -/
noncomputable def Scheme.openImageIsoOver
    {S : Scheme.{u}} {X Y : Over S} (e : X ≅ Y) (U : X.left.Opens) :
    Over.mk (U.ι ≫ X.hom) ≅
      Over.mk ((e.hom.left ''ᵁ U).ι ≫ Y.hom) :=
  Over.isoMk (e.hom.left.isoImage U) (by
    change (e.hom.left.isoImage U).hom ≫
      ((e.hom.left ''ᵁ U).ι ≫ Y.hom) = U.ι ≫ X.hom
    rw [← Category.assoc, Scheme.Hom.isoImage_hom_ι,
      Category.assoc, Over.w e.hom])

/-- A specified relatively very ample line bundle on an open subscheme
transports to its open image under an isomorphism over the base. -/
theorem Scheme.isHQuasiProjectiveWith_openImage
    {S : Scheme.{0}} {X Y : Over S} (e : X ≅ Y) (U : X.left.Opens)
    (L : U.toScheme.Modules)
    (hU : (U.ι ≫ X.hom).IsHQuasiProjectiveWith L) :
    (Over.mk ((e.hom.left ''ᵁ U).ι ≫ Y.hom)).hom.IsHQuasiProjectiveWith
      ((Scheme.Modules.pullback
        (Scheme.openImageIsoOver e U).inv.left).obj L) :=
  hU.of_over_iso (Scheme.openImageIsoOver e U).symm

namespace ProjectiveSpace

/-- **The structural morphism of relative projective space is itself
projective**, carrying the Serre twist `O(1)`: the canonical inhabitant of
`IsProjectiveWith`, with the identity closed immersion.  This exhibits
`ℙ(Fin (d+1); S) ↘ S` as the universal projective morphism and shows the
predicate is non-vacuous. -/
theorem isProjectiveWith_over (d : ℕ) (S : Scheme.{0}) :
    (ℙ(Fin (d + 1); S) ↘ S).IsProjectiveWith (twistingSheaf (Fin (d + 1)) S 1) :=
  ⟨Fin (d + 1), inferInstance, 𝟙 _, inferInstance, Category.id_comp _,
    ⟨((Scheme.Modules.pullbackId _).app _).symm⟩⟩

/-- Relative projective space is H-quasi-projective carrying `O(1)`. -/
theorem isHQuasiProjectiveWith_over (d : ℕ) (S : Scheme.{0}) :
    (ℙ(Fin (d + 1); S) ↘ S).IsHQuasiProjectiveWith
      (twistingSheaf (Fin (d + 1)) S 1) :=
  (isProjectiveWith_over d S).isHQuasiProjectiveWith

end ProjectiveSpace

end AlgebraicGeometry
