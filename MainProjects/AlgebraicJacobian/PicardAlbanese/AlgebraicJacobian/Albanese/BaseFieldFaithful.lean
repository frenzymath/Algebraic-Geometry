/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib

/-!
# Field base change is faithful (S10 substrate: the uniqueness half of Galois descent)

Milne's descent pattern for the Albanese universal property (III §6.4) is
*uniqueness-first*: one proves the factorisation `f = ofCurve P ≫ g` over `k̄`, where
the geometry is available, and then descends `g` to `k`.  The classical write-up runs
that descent through Galois cohomology — a cocycle for `Gal(k̄/k)`, a spreading-out
argument to a finite level, and Galois descent of the resulting morphism.

**The uniqueness half needs none of that.**  `∃!` splits into existence and
uniqueness, and *uniqueness descends for free along every field extension whatsoever*
— not just Galois ones, not just algebraic ones.  The reason is one line:

> `Spec L ⟶ Spec k` is flat and surjective for every field extension `k → L`, hence
> the base-change functor `Over (Spec k) ⥤ Over (Spec L)` is faithful.

Faithfulness is exactly the statement that an equation between two morphisms of
`k`-schemes may be checked after base change.  So a `k`-morphism out of the Jacobian
is pinned by its `k̄`-avatar, and the *uniqueness* clause of
`exists_unique_ofCurve_comp` over `k` follows from the uniqueness clause over `k̄`
with no Galois theory, no cocycles, and no finite-level spreading out.

What this file does *not* do is descend **existence**: producing a `k`-morphism from a
`k̄`-morphism is where the Galois cocycle genuinely lives, and no part of it is
addressed here.  The value of separating the two halves is that it removes the
uniqueness clause from the Galois budget entirely, and it does so at arbitrary — in
particular *infinite* — extensions, which is precisely the staging that the Wave-6
recon (`informal/w6-albanese-port-recon.md` §4.2) recorded as "pinned nowhere":
there is nothing to pin, because faithfulness does not care whether `k → k̄` is
finite.

## Main declarations

* `AlgebraicGeometry.epi_pullback_fst_algebraMap` — the base change of
  `Spec L ⟶ Spec k` along any `k`-scheme is an epimorphism (flat + surjective).
* `AlgebraicGeometry.faithful_baseChange` — **the substrate**: base change along any
  field extension `k → L` is a faithful functor `Over (Spec k) ⥤ Over (Spec L)`.
* `AlgebraicGeometry.eq_of_baseChange_map_eq` — its element form: two `k`-morphisms
  agreeing after base change to `L` are equal.
* `AlgebraicGeometry.subsingleton_of_subsingleton_baseChange` — the shape the
  descent consumes: a `Hom`-set over `k` is a subsingleton as soon as the
  base-changed `Hom`-set over `L` is.
* `AlgebraicGeometry.existsUnique_of_baseChange_subsingleton` — **the uniqueness-first
  descent step**: given existence over `k` and uniqueness over `L`, conclude `∃!`
  over `k`.

The base-change functor is spelled `Over.pullback (Spec.map (CommRingCat.ofHom
(algebraMap k L)))`, i.e. verbatim `AlgebraicGeometry.baseChange k L` of
`Challenge.lean:170`; this file is stated against the raw spelling so that it does not
import the statement file.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

section

variable (k L : Type u) [Field k] [Field L] [Algebra k L]

/-- The base change of the field extension morphism `Spec L ⟶ Spec k` along an
arbitrary `k`-scheme `Z` is an **epimorphism** of schemes.

Both hypotheses of `Flat.epi_of_flat_of_surjective` are stable under base change:
`Spec L ⟶ Spec k` is flat (a field extension is a flat ring map) and surjective (it
hits the unique point of `Spec k`), so its pullback `pr₁` along `Z ⟶ Spec k` is flat
and surjective too. -/
theorem epi_pullback_fst_algebraMap {Z : Scheme.{u}} (g : Z ⟶ Spec (.of k)) :
    Epi (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap k L)))) := by
  haveI : Flat (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap k L)))) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  haveI : Surjective (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap k L)))) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  exact Flat.epi_of_flat_of_surjective _

/-- **Base change along a field extension is faithful.**

For any extension of fields `k → L` — no finiteness, separability, normality or
algebraicity assumed — the functor `X ↦ X ×_{Spec k} Spec L` on `k`-schemes is
faithful.  This is mathlib's `Over.faithful_pullback` fed by
`epi_pullback_fst_algebraMap`: `Over.pullback f` is faithful as soon as every base
change of `f` is epi, and for `f = Spec L ⟶ Spec k` that is flatness plus
surjectivity.

This single instance is the whole uniqueness half of `k̄ → k` Galois descent: an
identity of morphisms of `k`-schemes may be verified over `k̄`. -/
instance faithful_baseChange :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).Faithful :=
  haveI : ∀ (Z : Scheme.{u}) (g : Z ⟶ Spec (.of k)),
      Epi (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap k L)))) :=
    fun _ g => epi_pullback_fst_algebraMap k L g
  Over.faithful_pullback _

variable {k L}

/-- **Descent of an equation of morphisms along a field extension**: if two morphisms
of `k`-schemes become equal after base change to `L`, they were already equal.  The
element form of `faithful_baseChange`. -/
theorem eq_of_baseChange_map_eq {X Y : Over (Spec (.of k))} {f g : X ⟶ Y}
    (h : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map f
      = (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map g) :
    f = g :=
  (faithful_baseChange k L).map_injective h

/-- **Descent of uniqueness**: if the `L`-points `X_L ⟶ Y_L` of the base-changed pair
form a subsingleton, so do the `k`-morphisms `X ⟶ Y`.

This is the form the Albanese descent consumes.  Note the direction: subsingleton-ness
is *pulled back* from the big field to the small one, which is why the geometric
uniqueness argument may be run over `k̄` and then read off over `k`. -/
theorem subsingleton_of_subsingleton_baseChange {X Y : Over (Spec (.of k))}
    (h : Subsingleton
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj X ⟶
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj Y)) :
    Subsingleton (X ⟶ Y) :=
  ⟨fun _ _ => eq_of_baseChange_map_eq (h.elim _ _)⟩

/-- **The uniqueness-first descent step, packaged.**

Milne 6.4's `∃!` over `k` is assembled from two inputs of quite different cost:

* `hex`, *existence over `k`* — the part that genuinely needs the Galois cocycle
  (or any other construction of a `k`-rational morphism), supplied by the caller;
* `hL`, *uniqueness over `L`* — the geometric argument, run over `k̄` where the
  symmetric-power/birationality machinery is available.

The conclusion is `∃!` over `k`.  Nothing here is specific to the Albanese setting:
`u` is any `k`-morphism and the predicate is factorisation through it. -/
theorem existsUnique_of_baseChange_subsingleton {X J A : Over (Spec (.of k))}
    (u : X ⟶ J) (f : X ⟶ A)
    (hex : ∃ g : J ⟶ A, f = u ≫ g)
    (hL : Subsingleton
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj J ⟶
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj A)) :
    ∃! g : J ⟶ A, f = u ≫ g := by
  obtain ⟨g, hg⟩ := hex
  exact ⟨g, hg, fun _ _ => (subsingleton_of_subsingleton_baseChange hL).elim _ _⟩

end

end AlgebraicGeometry
