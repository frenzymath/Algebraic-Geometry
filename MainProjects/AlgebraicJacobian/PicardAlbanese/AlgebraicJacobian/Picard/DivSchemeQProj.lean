/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivScheme
import AlgebraicJacobian.Picard.GrassmannianSeparated

/-!
# DD-Q: the `divQProj` quasi-projectivity bundle for `DivScheme g`

The certificate of `informal/dat-d-worksheet.md` §4.1: `DivScheme g` is delivered
quasi-projective **as consumed** — the closed immersion `divSchemeι` into the
Grassmannian pair together with the pair's finite affine frame atlas, quasi-compactness,
local finite-typeness over `k`, and separatedness, and the same three properties derived
on `DivScheme g` itself (closed immersions into qc/lft/separated transfer).

## The Grassmannian-pair data (§4.1 middle factor)

* `Grassmannian.isAffine_grPairCover_X`: each patch of the finite product atlas
  `grPairCover` is affine (with `finite_grPairCover_index`, `GrassmannianPair.lean:68`:
  the **finite affine frame atlas**).
* `Grassmannian.compactSpace_grPair`, `quasiCompact_grPairStructMap`: quasi-compactness
  is FREE — finitely many affine charts glue to a compact space; no image argument.
* `Grassmannian.locallyOfFiniteType_grPairStructMap`: charts are `Spec` of finite-type
  `k`-algebras (DD-3's `locallyOfFiniteType_grStructMap`), stable under base change and
  composition through the pair.
* `Grassmannian.isSeparated_grPairStructMap`, `isSeparated_grPair`: the GRQ
  affine-diagonal argument (DD-3's `isSeparated_grStructMap`) through the pullback.

## The derived bundle on `DivScheme g` (§4.2 consumer rows)

* `quasiCompact_carveSchemeOverHom` / `quasiCompact_divSchemeOverHom` and
  `compactSpace_carveScheme` / `compactSpace_divScheme`: the **Wave-5 qc inputs**
  toward `AbelSourceData.isProper` (`AbelianVariety/AbelSource.lean`).
* `locallyOfFiniteType_carveSchemeOverHom` / `locallyOfFiniteType_divSchemeOverHom`:
  the **DAT-glue lft certificate** for the 01JJ chart family.
* `isSeparated_carveSchemeOverHom` / `isSeparated_divSchemeOverHom` and
  `isSeparated_carveScheme` / `isSeparated_divScheme`: separatedness over `k` and
  absolute — with lft and qc, the `IsProper` constituents short of universal closedness.
* `DivQProjBundle` / `divQProj`: the §4.1 bundle verbatim, the single citable
  certificate for **DAT-G**'s quasi-projective charts.

## Honest boundary (§4.1, BINDING)

PROJECTIVITY of the Grassmannian (Plücker) is **not** delivered — nothing here is an
ample bundle or a valuative/universal-closedness certificate.  "Quasi-projective" is
consumed as the bundle above; if a consumer needs honest projectivity (or universal
closedness of `grPair`, e.g. for the properness of `Div^g` feeding
`AbelSourceData.isProper`), that is a NEW brick negotiated by that consumer's
worksheet, not silently absorbed here.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Grassmannian

section Pair

variable (k : Type u) [Field k] (d₁ r₁ d₂ r₂ : ℕ)

/-- Each patch of the finite product atlas `grPairCover` is **affine**: it is
isomorphic to `Spec (R^I ⊗[k] R^J)` via `grPairPatchIso`.  Together with
`finite_grPairCover_index` this is the §4.1 "finite affine frame atlas" of the pair. -/
instance isAffine_grPairCover_X (ij : (grPairCover k d₁ r₁ d₂ r₂).I₀) :
    IsAffine ((grPairCover k d₁ r₁ d₂ r₂).X ij) :=
  IsAffine.of_isIso (grPairPatchIso k d₁ r₁ d₂ r₂ ij.1 ij.2).hom

/-- **The Grassmannian pair is a compact space**: quasi-compactness is free from the
finite affine atlas (worksheet §4.1: no a-posteriori image argument) — the projection
`grPairFst` is quasi-compact by base change and `Gr(d₁, r₁)` is compact. -/
instance compactSpace_grPair : CompactSpace (grPair k d₁ r₁ d₂ r₂) := by
  haveI := quasiCompact_grStructMap k d₂ r₂
  haveI : QuasiCompact (grPairFst k d₁ r₁ d₂ r₂) :=
    inferInstanceAs (QuasiCompact (pullback.fst (grStructMap k d₁ r₁) (grStructMap k d₂ r₂)))
  exact QuasiCompact.compactSpace_of_compactSpace (grPairFst k d₁ r₁ d₂ r₂)

/-- The structure morphism `grPair → Spec k` is **quasi-compact** (§4.1 bundle row:
free from the finite affine atlas). -/
theorem quasiCompact_grPairStructMap : QuasiCompact (grPairStructMap k d₁ r₁ d₂ r₂) := by
  have : CompactSpace (grPair k d₁ r₁ d₂ r₂) := compactSpace_grPair k d₁ r₁ d₂ r₂
  exact HasAffineProperty.iff_of_isAffine.mpr this

/-- The structure morphism `grPair → Spec k` is **locally of finite type** (§4.1 bundle
row): DD-3's chart computation `locallyOfFiniteType_grStructMap`, transferred through
the pullback projection (stable under base change) and composition. -/
theorem locallyOfFiniteType_grPairStructMap :
    LocallyOfFiniteType (grPairStructMap k d₁ r₁ d₂ r₂) := by
  haveI := locallyOfFiniteType_grStructMap k d₁ r₁
  haveI := locallyOfFiniteType_grStructMap k d₂ r₂
  haveI : LocallyOfFiniteType (grPairFst k d₁ r₁ d₂ r₂) :=
    inferInstanceAs
      (LocallyOfFiniteType (pullback.fst (grStructMap k d₁ r₁) (grStructMap k d₂ r₂)))
  exact inferInstanceAs
    (LocallyOfFiniteType (grPairFst k d₁ r₁ d₂ r₂ ≫ grStructMap k d₁ r₁))

/-- The structure morphism `grPair → Spec k` is **separated** (§4.1 bundle row): DD-3's
affine-diagonal patch computation `isSeparated_grStructMap`, transferred through the
pullback projection (stable under base change) and composition. -/
theorem isSeparated_grPairStructMap : IsSeparated (grPairStructMap k d₁ r₁ d₂ r₂) := by
  haveI := isSeparated_grStructMap k d₁ r₁
  haveI := isSeparated_grStructMap k d₂ r₂
  haveI : IsSeparated (grPairFst k d₁ r₁ d₂ r₂) :=
    inferInstanceAs (IsSeparated (pullback.fst (grStructMap k d₁ r₁) (grStructMap k d₂ r₂)))
  exact inferInstanceAs (IsSeparated (grPairFst k d₁ r₁ d₂ r₂ ≫ grStructMap k d₁ r₁))

/-- **The Grassmannian pair is separated** (absolutely): the structure morphism is
separated and `Spec k` is affine, hence separated over the terminal object. -/
theorem isSeparated_grPair : (grPair k d₁ r₁ d₂ r₂).IsSeparated := by
  haveI := isSeparated_grPairStructMap k d₁ r₁ d₂ r₂
  rw [Scheme.isSeparated_iff, ← terminal.comp_from (grPairStructMap k d₁ r₁ d₂ r₂)]
  infer_instance

end Pair

end Grassmannian

/-! ## The derived bundle on the glued carve locus (generic level) -/

section Carve

open Grassmannian

variable (k : Type u) [Field k] (g r₁ r₂ : ℕ)
variable {ι : Type u} (μ : ι → ((Fin r₁ → k) →ₗ[k] (Fin r₂ → k)))

/-- The structure morphism of the glued carve locus is **quasi-compact**: the closed
immersion `carveSchemeι` is affine (hence qc), composed with the qc structure morphism
of the pair. -/
theorem quasiCompact_carveSchemeOverHom :
    QuasiCompact (carveSchemeOver k g r₁ r₂ μ).hom := by
  haveI := quasiCompact_grPairStructMap k g r₁ g r₂
  exact inferInstanceAs
    (QuasiCompact (carveSchemeι k g r₁ r₂ μ ≫ grPairStructMap k g r₁ g r₂))

/-- **The glued carve locus is a compact space**: a closed subscheme of the compact
Grassmannian pair (§4.1: closed subscheme of qc is qc). -/
instance compactSpace_carveScheme : CompactSpace (carveScheme k g r₁ r₂ μ) :=
  QuasiCompact.compactSpace_of_compactSpace (carveSchemeι k g r₁ r₂ μ)

/-- The structure morphism of the glued carve locus is **locally of finite type**:
closed immersions are locally of finite type, and lft is stable under composition. -/
theorem locallyOfFiniteType_carveSchemeOverHom :
    LocallyOfFiniteType (carveSchemeOver k g r₁ r₂ μ).hom := by
  haveI := locallyOfFiniteType_grPairStructMap k g r₁ g r₂
  exact inferInstanceAs
    (LocallyOfFiniteType (carveSchemeι k g r₁ r₂ μ ≫ grPairStructMap k g r₁ g r₂))

/-- The structure morphism of the glued carve locus is **separated**: closed immersions
are monomorphisms (hence separated), composed with the separated structure morphism of
the pair. -/
theorem isSeparated_carveSchemeOverHom :
    IsSeparated (carveSchemeOver k g r₁ r₂ μ).hom := by
  haveI := isSeparated_grPairStructMap k g r₁ g r₂
  exact inferInstanceAs
    (IsSeparated (carveSchemeι k g r₁ r₂ μ ≫ grPairStructMap k g r₁ g r₂))

/-- **The glued carve locus is separated** (absolutely). -/
theorem isSeparated_carveScheme : (carveScheme k g r₁ r₂ μ).IsSeparated := by
  haveI : IsSeparated (carveSchemeι k g r₁ r₂ μ ≫ grPairStructMap k g r₁ g r₂) :=
    isSeparated_carveSchemeOverHom k g r₁ r₂ μ
  rw [Scheme.isSeparated_iff,
    ← terminal.comp_from (carveSchemeι k g r₁ r₂ μ ≫ grPairStructMap k g r₁ g r₂)]
  infer_instance

end Carve

/-! ## The campaign spellings (the DAT-D windows) and the §4.1 bundle -/

section Curve

open Scheme Grassmannian

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k))] [IsIntegral X]
variable (A B : X.CurveDivisor) (g r₁ r₂ : ℕ)
variable (b₁ : Module.Basis (Fin r₁) k ↥(divisorSections k B ⊤))
variable (b₂ : Module.Basis (Fin r₂) k ↥(divisorSections k (A + B) ⊤))

/-- The structure morphism of `DivScheme g` is **quasi-compact** — the Wave-5 qc input
toward `AbelSourceData.isProper` (§4.2 consumer row). -/
instance quasiCompact_divSchemeOverHom :
    QuasiCompact (divSchemeOver k A B g r₁ r₂ b₁ b₂).hom :=
  quasiCompact_carveSchemeOverHom k g r₁ r₂ (divCarveMul k A B r₁ r₂ b₁ b₂)

/-- **`DivScheme g` is a compact space**: a closed subscheme of the compact
Grassmannian pair (§4.1: qc is free, no image argument). -/
instance compactSpace_divScheme : CompactSpace (DivScheme k A B g r₁ r₂ b₁ b₂) :=
  compactSpace_carveScheme k g r₁ r₂ (divCarveMul k A B r₁ r₂ b₁ b₂)

/-- The structure morphism of `DivScheme g` is **locally of finite type** — the
DAT-glue lft certificate of the 01JJ chart family (§4.2 consumer row). -/
instance locallyOfFiniteType_divSchemeOverHom :
    LocallyOfFiniteType (divSchemeOver k A B g r₁ r₂ b₁ b₂).hom :=
  locallyOfFiniteType_carveSchemeOverHom k g r₁ r₂ (divCarveMul k A B r₁ r₂ b₁ b₂)

/-- The structure morphism of `DivScheme g` is **separated** — with
`quasiCompact_divSchemeOverHom` and `locallyOfFiniteType_divSchemeOverHom`, the
`IsProper` constituents short of universal closedness (§4.1 boundary). -/
instance isSeparated_divSchemeOverHom :
    IsSeparated (divSchemeOver k A B g r₁ r₂ b₁ b₂).hom :=
  isSeparated_carveSchemeOverHom k g r₁ r₂ (divCarveMul k A B r₁ r₂ b₁ b₂)

/-- **`DivScheme g` is separated** (absolutely). -/
instance isSeparated_divScheme : (DivScheme k A B g r₁ r₂ b₁ b₂).IsSeparated :=
  isSeparated_carveScheme k g r₁ r₂ (divCarveMul k A B r₁ r₂ b₁ b₂)

/-- **The `divQProj` certificate shape** (worksheet §4.1, verbatim): `DivScheme g` is
quasi-projective **as consumed** — the closed immersion into the Grassmannian pair,
the pair's finite affine frame atlas / qc / lft / separatedness data, and the derived
qc / lft / separatedness of `DivScheme g` over `k`.

Honest boundary (§4.1, BINDING): projectivity (Plücker) is NOT part of this bundle;
consumers needing an ample bundle or universal closedness must negotiate a new brick. -/
structure DivQProjBundle : Prop where
  /-- `DivScheme g ⟶ grPair` is a closed immersion (§3.1, closed in the pair). -/
  isClosedImmersion_ι : IsClosedImmersion (divSchemeι k A B g r₁ r₂ b₁ b₂)
  /-- The pair's frame atlas is finite. -/
  finite_atlasIndex : Finite (grPairCover k g r₁ g r₂).I₀
  /-- Each patch of the pair's frame atlas is affine. -/
  isAffine_atlas : ∀ ij : (grPairCover k g r₁ g r₂).I₀,
    IsAffine ((grPairCover k g r₁ g r₂).X ij)
  /-- The pair is quasi-compact over `k`. -/
  quasiCompact_pairStructMap : QuasiCompact (grPairStructMap k g r₁ g r₂)
  /-- The pair is locally of finite type over `k`. -/
  locallyOfFiniteType_pairStructMap : LocallyOfFiniteType (grPairStructMap k g r₁ g r₂)
  /-- The pair is separated over `k`. -/
  isSeparated_pairStructMap : IsSeparated (grPairStructMap k g r₁ g r₂)
  /-- `DivScheme g` is quasi-compact over `k` (Wave-5 row). -/
  quasiCompact_hom : QuasiCompact (divSchemeOver k A B g r₁ r₂ b₁ b₂).hom
  /-- `DivScheme g` is locally of finite type over `k` (DAT-glue row). -/
  locallyOfFiniteType_hom : LocallyOfFiniteType (divSchemeOver k A B g r₁ r₂ b₁ b₂).hom
  /-- `DivScheme g` is separated over `k`. -/
  isSeparated_hom : IsSeparated (divSchemeOver k A B g r₁ r₂ b₁ b₂).hom

/-- **`divQProj`** (worksheet §4.1): the quasi-projectivity bundle of `DivScheme g`,
assembled — the single citable certificate for DAT-G's quasi-projective charts
(§4.2 consumer row, with the §4.1 Plücker boundary note). -/
theorem divQProj : DivQProjBundle k A B g r₁ r₂ b₁ b₂ where
  isClosedImmersion_ι := isClosedImmersion_divSchemeι k A B g r₁ r₂ b₁ b₂
  finite_atlasIndex := finite_grPairCover_index k g r₁ g r₂
  isAffine_atlas ij := isAffine_grPairCover_X k g r₁ g r₂ ij
  quasiCompact_pairStructMap := quasiCompact_grPairStructMap k g r₁ g r₂
  locallyOfFiniteType_pairStructMap := locallyOfFiniteType_grPairStructMap k g r₁ g r₂
  isSeparated_pairStructMap := isSeparated_grPairStructMap k g r₁ g r₂
  quasiCompact_hom := quasiCompact_divSchemeOverHom k A B g r₁ r₂ b₁ b₂
  locallyOfFiniteType_hom := locallyOfFiniteType_divSchemeOverHom k A B g r₁ r₂ b₁ b₂
  isSeparated_hom := isSeparated_divSchemeOverHom k A B g r₁ r₂ b₁ b₂

end Curve

end AlgebraicGeometry
