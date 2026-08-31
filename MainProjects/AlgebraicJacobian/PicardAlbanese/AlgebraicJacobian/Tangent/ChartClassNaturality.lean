/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.EffectivityMoving

/-!
# Naturality of the affine-open Čech–Picard class in the SCHEME (W5-T4, (iii-c2-aff-geo) step 1)

`informal/w5-t4-worksheet.md` §6.17 named T4's last mathematical residue as a naturality square
for `Scheme.Opens.cechPicClass`, and stated it as a Lean statement one could type:

> for `g : X ⟶ Z` and an affine open `O` of `Z` with affine preimage,
> `(g ⁻¹ᵁ O).cechPicClass _ (CechPic.map g L) = Pic.mapRingHom (g.appLE O _ _) (O.cechPicClass _ L)`

That square is `Opens.cechPicClass_map` below. `Picard/EffectivityMoving.lean` has the *restriction*
seam `Opens.cechPicClass_of_le` — along `O' ≤ O` inside one scheme; nothing along a scheme
morphism. This file supplies the missing face.

## The `appLE`/`ιTop` square was already in mathlib, under a name §6.17 did not find

§6.17 got the Picard-side reduction all the way down to a pure `CommRingCat` equality,

```
O.ιTop ≫ (g.resLE O (g⁻¹O) le_rfl).appTop = g.appLE O (g⁻¹O) le_rfl ≫ (g⁻¹O).ιTop
```

reported `exact?` failing on it, and prescribed `Scheme.Hom.appLE_comp_appLE` plus an
`appLE_congr_hom` transported along `resLE_comp_ι`. It then measured that route costing **more than
1 600 000 heartbeats without finishing**, and recorded the item as elaboration-expensive.

**That route is not needed.** Mathlib's `Scheme.Hom.resLE_app_top` is
`(f.resLE U V e).app ⊤ = U.topIso.hom ≫ f.appLE U V e ≫ V.topIso.inv` — the same square, stated
for `topIso` instead of the project's `ιTop`. Since `ιTop` and `topIso.inv` agree (one `simp`
plus `rfl`; they are *not* syntactically equal, hence `ιTop_resLE_appTop` below rather than a
direct rewrite), the whole step is three rewrites and no heartbeat budget. Measured: the default
200000 suffices for both declarations in this file.

> **The method point, since §6.17's prescription was a correct diagnosis with a wrong price.** The
> leftover goal was recognised as "the `appLE`/`ιTop` square", searched for under the project's own
> spelling (`ιTop`), and not found — because mathlib states it in the spelling mathlib uses
> (`topIso`). Search for the *shape* under the UPSTREAM vocabulary too, not only your own; the
> preceding session's cost estimate was measured honestly and was measuring the wrong route.

## Main declarations

* `AlgebraicGeometry.Scheme.ιTop_resLE_appTop` — the `appLE`/`ιTop` square for `g.resLE`.
* `AlgebraicGeometry.Scheme.Opens.cechPicClass_map` — the naturality square, §6.17's statement.

Reference: `informal/w5-t4-worksheet.md` §§6.17, 6.27.
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace Scheme

variable {X Z : Scheme.{u}} (g : X ⟶ Z)

/-- **The `appLE`/`ιTop` square for the restriction of `g` to an open and its preimage.**

This is §6.17 step 3's leftover `CommRingCat` equality. It is mathlib's `Hom.resLE_app_top` after
identifying `Opens.ιTop` with `Opens.topIso.inv`: both are `Z.presheaf`-maps of the canonical
comparison `O.ι ''ᵁ ⊤ = O`, but one is spelled with `homOfLE` and the other with `eqToHom`, so the
identification is a `simp`-then-`rfl` and not syntactic. -/
theorem ιTop_resLE_appTop (O : Z.Opens) :
    O.ιTop ≫ (g.resLE O (g ⁻¹ᵁ O) le_rfl).appTop
      = g.appLE O (g ⁻¹ᵁ O) le_rfl ≫ (g ⁻¹ᵁ O).ιTop := by
  rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
  have h1 : O.ιTop = O.topIso.inv := by
    simp [Scheme.Opens.ιTop, Scheme.Opens.topIso]; rfl
  have h2 : (g ⁻¹ᵁ O).ιTop = (g ⁻¹ᵁ O).topIso.inv := by
    simp [Scheme.Opens.ιTop, Scheme.Opens.topIso]; rfl
  rw [h1, h2, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- **Naturality of `Opens.cechPicClass` in the scheme** — the square worksheet §6.17 isolated as
the last mathematical residue of clause (iii-c2-aff).

For `g : X ⟶ Z`, an affine open `O ⊆ Z` whose preimage `g ⁻¹ᵁ O` is *also* affine (not automatic;
at the thickened charts of the tangent computation it comes from `relCover`'s `isAffineOpen₀/₁`),
the chart class of the pulled-back Čech–Picard class is the base change of the chart class along
the section map `g.appLE O (g ⁻¹ᵁ O)`.

The proof is the model of `Opens.cechPicClass_of_le`: collapse the two pullbacks, factor
`(g⁻¹O).ι ≫ g = g.resLE ≫ O.ι` (`Hom.resLE_comp_ι`), push `CechPic.toPic` through the `resLE`
(`CechPic.toPic_map`, which needs both schemes affine — that is what `hO`/`hgO` buy), and finish
with `ιTop_resLE_appTop` in its inverse form. -/
theorem Opens.cechPicClass_map (O : Z.Opens) (hO : IsAffineOpen O)
    (hgO : IsAffineOpen (g ⁻¹ᵁ O)) (L : Z.CechPic) :
    (g ⁻¹ᵁ O).cechPicClass hgO (Scheme.CechPic.map g L)
      = CommRing.Pic.mapRingHom (g.appLE O (g ⁻¹ᵁ O) le_rfl).hom
          (O.cechPicClass hO L) := by
  haveI : IsAffine (O : Scheme.{u}) := hO
  haveI : IsAffine ((g ⁻¹ᵁ O) : Scheme.{u}) := hgO
  rw [Opens.cechPicClass, Opens.cechPicClass]
  have hcollapse : Scheme.CechPic.map (g ⁻¹ᵁ O).ι (Scheme.CechPic.map g L)
      = Scheme.CechPic.map ((g ⁻¹ᵁ O).ι ≫ g) L := by
    rw [Scheme.CechPic.map_comp]; rfl
  rw [hcollapse, ← Scheme.Hom.resLE_comp_ι g (U := O) (V := g ⁻¹ᵁ O) le_rfl,
    Scheme.CechPic.map_comp, MonoidHom.comp_apply,
    Scheme.CechPic.toPic_map (g.resLE O (g ⁻¹ᵁ O) le_rfl),
    CommRing.Pic.mapRingHom_mapRingHom, CommRing.Pic.mapRingHom_mapRingHom]
  refine congrArg (fun ψ => CommRing.Pic.mapRingHom ψ
    (Scheme.CechPic.toPic O.toScheme (Scheme.CechPic.map O.ι L))) ?_
  have hinv : (g.resLE O (g ⁻¹ᵁ O) le_rfl).appTop ≫ inv (g ⁻¹ᵁ O).ιTop
      = inv O.ιTop ≫ g.appLE O (g ⁻¹ᵁ O) le_rfl := by
    rw [IsIso.comp_inv_eq, Category.assoc, ← ιTop_resLE_appTop g O, IsIso.inv_hom_id_assoc]
  have h3 := congrArg CommRingCat.Hom.hom hinv
  rwa [CommRingCat.hom_comp, CommRingCat.hom_comp] at h3

end Scheme

end AlgebraicGeometry
