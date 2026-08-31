/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Tangent.DualNumberUnitTransport

/-!
# Čech Picard groups transport along an isomorphism (W5-T3, step (T3-4))

`Tangent/DualNumberUnitTransport.lean` builds the `(3c)` seam
`transportLeft k C : (C ⊗ 𝟙_)ₗ ⟶ relCurve C k` and proves it an **isomorphism**
(`isIso_transportLeft`), with a docstring saying why that matters: *"a consumer may transport a
kernel or injectivity statement across the seam in either direction — which is what a kernel
comparison needs."*

The sentence that cashes that in was missing. This file writes it: **`Scheme.CechPic.map` along an
isomorphism is a group isomorphism** — `Pic.lean` has `map_id` and `map_comp` and nothing that
composes them into invertibility, and a search of both projects and mathlib finds only
`classDeg_cechPicMap_of_isIso` (about *degrees*, not about the map being bijective). See
`informal/w5-t4-worksheet.md` §7.2.

## Why an equivalence and not just injectivity

The Wave-5 statement is a **kernel** comparison, and `ker(A → B) ≃ ker(A' → B)` needs the transport
to travel in both directions: injectivity alone would give one inclusion of kernels. So the headline
here is `cechPicMapEquivOfIso`, a `MulEquiv`, with `cechPicMap_injective_of_isIso` /
`cechPicMap_surjective_of_isIso` as the two faces a consumer may want separately. This is the
standing lesson of inbox `I-0571`: an isomorphism of the two *ends* of a map says nothing about the
map, and the object a kernel computation consumes is the *arrow*.

## Implementation notes

`CechPic.map_comp` is stated in the `MonoidHom.comp` spelling
(`map (f ≫ g) = (map f).comp (map g)`), which does **not** reduce to the applied form on its own —
`rw [CechPic.map_comp]` leaves a `MonoidHom.comp` head where the goal has an application. Hence the
`show … from by rw [CechPic.map_comp]; rfl` step: the `rfl` is what strips `MonoidHom.comp`.
Measured on the scratch olean root; the direct `rw [← CechPic.map_comp]` at the application
fails with *"did
not find an occurrence of the pattern"* and names the `MonoidHom.comp` pattern in the message, which
is the tell.

Both round-trip identities are proved from the *same* helper applied at `f` and at `inv f`, so the
`MulEquiv` costs one lemma rather than two.

## Scope: this file does NOT identify the two opens

`transportLeft`'s target is `relCurve C k`, and the tangent chain's other leg lands on `C.left`.
Those carriers are the same scheme, but at the level of **opens** the base-change leg is *not*
definitional: measured this session,

```lean
example (V : C.left.Opens) :
    relCurveMap C k[ε] k ⁻¹ᵁ ((fst C (overSpec k k[ε])).left ⁻¹ᵁ V)
      = (fst C (overSpec k k)).left ⁻¹ᵁ V := rfl        -- FAILS
```

— it is the theorem `relCurveMap_preimage` (`Cohomology/RelativeSectionsLinear.lean`). So a consumer
instantiating this file at the Wave-5 seam still owes that transport; it is named here rather than
hidden, and it is genuinely one `rw`, not `rfl`. (The *overlap* costs nothing: preimage does
distribute over `⊓` by `rfl`.)

Nothing here is about dual numbers, curves, or `k`: `X`, `Y` are arbitrary schemes and `f` an
arbitrary isomorphism.

## Main declarations

* `AlgebraicGeometry.Scheme.cechPicMap_map_inv` — the round trip, the one helper.
* `AlgebraicGeometry.Scheme.cechPicMap_injective_of_isIso` /
  `AlgebraicGeometry.Scheme.cechPicMap_surjective_of_isIso` — the two faces.
* `AlgebraicGeometry.Scheme.cechPicMapEquivOfIso` — **(T3-4)**: `Y.CechPic ≃* X.CechPic` along an
  isomorphism `f : X ⟶ Y`.
* `AlgebraicGeometry.cechPicMap_transportLeft_injective` — the Wave-5 instance, at the `(3c)` seam.

Reference: Kleiman, "The Picard scheme", §5 Thm. 5.11 (arXiv:math/0504020);
`informal/w5-t4-worksheet.md` §§6.24, 6.26, 7.2.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

namespace Scheme

variable {X Y : Scheme.{u}}

/-- **The round trip along an isomorphism.** Pulling a Čech Picard class back along `f` and then
along `inv f` returns it.

`CechPic.map_comp` is stated with a `MonoidHom.comp` head, so the rewrite has to be routed through
an explicit `show`; see the module docstring for the exact failure the direct `rw` gives. -/
theorem cechPicMap_map_inv (f : X ⟶ Y) [IsIso f] (L : Y.CechPic) :
    CechPic.map (inv f) (CechPic.map f L) = L := by
  rw [show CechPic.map (inv f) (CechPic.map f L) = CechPic.map (inv f ≫ f) L from by
      rw [CechPic.map_comp]; rfl,
    IsIso.inv_hom_id, CechPic.map_id]
  rfl

/-- **Pullback along an isomorphism is injective on Čech Picard classes.** One face of
`cechPicMapEquivOfIso`, named because a kernel *inclusion* consumes exactly this. -/
theorem cechPicMap_injective_of_isIso (f : X ⟶ Y) [IsIso f] :
    Function.Injective (CechPic.map f) := by
  intro a b h
  have h2 := congrArg (CechPic.map (inv f)) h
  rwa [cechPicMap_map_inv f a, cechPicMap_map_inv f b] at h2

/-- **Pullback along an isomorphism is surjective on Čech Picard classes** — the preimage of `L` is
its pullback along `inv f`, by the same round-trip helper read at `inv f`. -/
theorem cechPicMap_surjective_of_isIso (f : X ⟶ Y) [IsIso f] :
    Function.Surjective (CechPic.map f) := fun L =>
  ⟨CechPic.map (inv f) L, by
    haveI : IsIso (inv f) := inferInstance
    have h := cechPicMap_map_inv (inv f) L
    rwa [IsIso.inv_inv] at h⟩

/-- **(T3-4): the Čech Picard groups of isomorphic schemes are isomorphic, ALONG the given
isomorphism.**

Stated as a `MulEquiv` rather than as the two `Function.Injective`/`Surjective` faces because a
kernel comparison must travel in both directions (`I-0571`): a bare bijection of the two ends of a
map is not usable, and what makes this one usable is that it *is* `CechPic.map f`, so it commutes
with everything `CechPic.map` commutes with by `map_comp`. -/
noncomputable def cechPicMapEquivOfIso (f : X ⟶ Y) [IsIso f] : Y.CechPic ≃* X.CechPic :=
  MulEquiv.ofBijective (CechPic.map f)
    ⟨cechPicMap_injective_of_isIso f, cechPicMap_surjective_of_isIso f⟩

@[simp]
theorem cechPicMapEquivOfIso_apply (f : X ⟶ Y) [IsIso f] (L : Y.CechPic) :
    cechPicMapEquivOfIso f L = CechPic.map f L :=
  rfl

end Scheme

/-! ## The Wave-5 instance: the `(3c)` seam -/

variable {k : Type u} [Field k] (C : Over (Spec (CommRingCat.of k)))

/-- **The `(3c)` seam transports Čech Picard classes injectively.**
`Tangent/DualNumberUnitTransport.lean` proved `transportLeft` an isomorphism and said a consumer
"may transport a kernel … in either direction"; this is that sentence at the `CechPic` level, and it
is the step the Wave-5 `ε`-kernel chain crosses to get from `relCurve C k` back to the monoidal-unit
end.

The general lemma is the content; this instance exists so that the seam has a *consumer* rather than
being a landed carrier nothing reads (`I-0630`/`I-0711`). -/
theorem cechPicMap_transportLeft_injective :
    Function.Injective (Scheme.CechPic.map (transportLeft k C)) :=
  Scheme.cechPicMap_injective_of_isIso _

/-- The same seam as a group isomorphism of Čech Picard groups. -/
noncomputable def cechPicTransportLeftEquiv :
    (relCurve C k).CechPic ≃* (C ⊗ Over.mk (𝟙 (Spec (CommRingCat.of k)))).left.CechPic :=
  Scheme.cechPicMapEquivOfIso (transportLeft k C)

end AlgebraicGeometry
