/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.MayerVietoris
import AlgebraicJacobian.Cohomology.AffineVanishing

/-!
# The two-affine-cover H¹ cokernel bridge

For a scheme `X` over `Spec k` covered by two affine opens `U₀ ⊔ U₁ = ⊤`, this file
computes the degree-one cohomology of the structure sheaf (as a sheaf of `k`-modules on
the small Zariski site, `Sheaf.HModule`) as an explicit cokernel of a map of section
modules:

`H¹ₖ(X, 𝒪ₖ) ≃ₗ[k] Γ(X, U₀ ⊓ U₁) ⧸ range((s₀, s₁) ↦ s₀|_{U₀⊓U₁} - s₁|_{U₀⊓U₁})`

(`AlgebraicGeometry.TwoCover.h1CokEquiv`, with the cokernel carrier
`AlgebraicGeometry.TwoCover.H1Cok`). This is the computational access point for the genus
of a curve: `genus C = finrank k H¹ₖ(C, 𝒪_C)` becomes the corank of an explicit map of
function spaces.

**Hypotheses actually used**: `X` any scheme over `Spec k`, `IsAffineOpen U₀`,
`IsAffineOpen U₁`, `U₀ ⊔ U₁ = ⊤`. In particular *no* affineness (or even
quasi-compactness) hypothesis on the intersection `U₀ ⊓ U₁` is needed — unlike for the
classical Čech-complex identification, the derived-functor Mayer–Vietoris sequence of
`AlgebraicJacobian.Cohomology.MayerVietoris` is exact regardless, and affineness of the
two pieces alone kills their `H¹'` (`IsAffineOpen.subsingleton_moduleKSheaf_hModule'_one`).

## Main declarations

* `Scheme.twoCoverSquare` — the Mayer–Vietoris square `(U₀ ⊓ U₁, U₀, U₁, ⊤)` on the
  small Zariski site of `X`, for a covering pair of opens.
* `Scheme.twoCoverH1LinearEquiv` — the general-coefficients form: for any sheaf `F` of
  `k`-modules with `H¹'(U₀, F)` and `H¹'(U₁, F)` subsingletons,
  `HModule F 1 ≃ₗ[k] F(U₀ ⊓ U₁) ⧸ range(moduleDiff)` (reusable for twisted sheaves).
* `TwoCover.diff k X U₀ U₁` — the difference map `Γ(U₀) × Γ(U₁) →ₗ[k] Γ(U₀ ⊓ U₁)`.
* `TwoCover.H1Cok k X U₀ U₁` — the cokernel carrier `Γ(U₀ ⊓ U₁) ⧸ range diff`.
* `TwoCover.delta` — the connecting map `Γ(U₀ ⊓ U₁) →ₗ[k] HModule (X.moduleKSheaf k) 1`
  ("class of a section on the overlap").
* `TwoCover.h1CokEquiv : HModule (X.moduleKSheaf k) 1 ≃ₗ[k] H1Cok k X U₀ U₁`.
* Compatibility: `h1CokEquiv_delta` (`h1CokEquiv ∘ delta = Quotient.mk`),
  `delta_surjective`, `delta_diff`, `delta_resHom_left/right` and
  `h1Cok_mk_resHom_left/right` (classes of sections extending to `U₀` or `U₁` vanish).

The `k`-module structure on `Γ(X, U)` is `Scheme.overModule` (restriction of scalars
along the structure morphism), activated as a local instance as in
`AlgebraicJacobian.Cohomology.ModuleKSheaf`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

open CategoryTheory.GrothendieckTopology

section Square

variable (X : Scheme.{u}) (U₀ U₁ : X.Opens)

/-- The Mayer–Vietoris square `(U₀ ⊓ U₁, U₀, U₁, ⊤)` on the small Zariski site of a
scheme `X`, for two opens covering `X`. -/
noncomputable def Scheme.twoCoverSquare (hcov : U₀ ⊔ U₁ = ⊤) :
    (Opens.grothendieckTopology (X : TopCat)).MayerVietorisSquare :=
  Opens.mayerVietorisSquare'
    { X₁ := U₀ ⊓ U₁
      X₂ := U₀
      X₃ := U₁
      X₄ := ⊤
      f₁₂ := homOfLE inf_le_left
      f₁₃ := homOfLE inf_le_right
      f₂₄ := homOfLE le_top
      f₃₄ := homOfLE le_top
      fac := Subsingleton.elim _ _ } hcov.symm rfl

end Square

section GeneralCoefficients

variable (k : Type u) [CommRing k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
variable (U₀ U₁ : X.Opens)

/-- **The two-cover H¹ computation, general coefficients.** For a sheaf `F` of
`k`-modules on the small Zariski site of `X`, two opens with `U₀ ⊔ U₁ = ⊤` and
vanishing `H¹'(U₀, F)`, `H¹'(U₁, F)`, the degree-one cohomology of the site is the
cokernel of the restriction-difference map `F(U₀) × F(U₁) → F(U₀ ⊓ U₁)`. -/
noncomputable def Scheme.twoCoverH1LinearEquiv
    (F : Sheaf (Opens.grothendieckTopology (X : TopCat)) (ModuleCat.{u} k))
    (hcov : U₀ ⊔ U₁ = ⊤)
    [Subsingleton (Sheaf.HModule' F U₀ 1)] [Subsingleton (Sheaf.HModule' F U₁ 1)] :
    Sheaf.HModule F 1 ≃ₗ[k]
      (F.obj.obj (op (U₀ ⊓ U₁)) ⧸
        LinearMap.range ((X.twoCoverSquare U₀ U₁ hcov).moduleDiff F)) :=
  letI : Subsingleton (Sheaf.HModule' F (X.twoCoverSquare U₀ U₁ hcov).X₂ 1) :=
    inferInstanceAs (Subsingleton (Sheaf.HModule' F U₀ 1))
  letI : Subsingleton (Sheaf.HModule' F (X.twoCoverSquare U₀ U₁ hcov).X₃ 1) :=
    inferInstanceAs (Subsingleton (Sheaf.HModule' F U₁ 1))
  (Sheaf.HModule.linearEquivHModule' (isTerminalTop : IsTerminal (⊤ : X.Opens)) F 1).trans
    ((X.twoCoverSquare U₀ U₁ hcov).h1LinearEquiv F).symm

end GeneralCoefficients

namespace TwoCover

variable (k : Type u) [CommRing k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
variable (U₀ U₁ : X.Opens)

attribute [local instance] Scheme.overModule

/-- The restriction-difference map `Γ(X, U₀) × Γ(X, U₁) →ₗ[k] Γ(X, U₀ ⊓ U₁)`,
`(s₀, s₁) ↦ s₀|_{U₀ ⊓ U₁} - s₁|_{U₀ ⊓ U₁}` (see `TwoCover.diff_apply`), with the
`k`-module structures of `Scheme.overModule`. -/
noncomputable def diff : (Γ(X, U₀) × Γ(X, U₁)) →ₗ[k] Γ(X, U₀ ⊓ U₁) :=
  ((X.moduleKSheaf k).obj.map (homOfLE (inf_le_left : U₀ ⊓ U₁ ≤ U₀)).op).hom.comp
      (LinearMap.fst k _ _) -
    ((X.moduleKSheaf k).obj.map (homOfLE (inf_le_right : U₀ ⊓ U₁ ≤ U₁)).op).hom.comp
      (LinearMap.snd k _ _)

lemma diff_apply (t : Γ(X, U₀) × Γ(X, U₁)) :
    diff k X U₀ U₁ t = X.resHom inf_le_left t.1 - X.resHom inf_le_right t.2 :=
  rfl

/-- The two-cover difference map is the Mayer–Vietoris restriction-difference map of the
associated square. -/
lemma diff_eq_moduleDiff (hcov : U₀ ⊔ U₁ = ⊤) :
    diff k X U₀ U₁ = (X.twoCoverSquare U₀ U₁ hcov).moduleDiff (X.moduleKSheaf k) :=
  rfl

/-- **The two-cover H¹ cokernel carrier**: the cokernel of the restriction-difference
map, `Γ(X, U₀ ⊓ U₁) ⧸ range (TwoCover.diff)`. For `U₀, U₁` an affine open cover this is
`H¹ₖ(X, 𝒪)` (see `TwoCover.h1CokEquiv`); it is a plain quotient of section modules, so
`Module.finrank` arguments can be run on it directly. -/
noncomputable abbrev H1Cok : Type u :=
  Γ(X, U₀ ⊓ U₁) ⧸ LinearMap.range (diff k X U₀ U₁)

/-- A section extending to `U₀` has vanishing class in `H1Cok`. -/
lemma h1Cok_mk_resHom_left (t : Γ(X, U₀)) :
    (Submodule.Quotient.mk (X.resHom inf_le_left t) : H1Cok k X U₀ U₁) = 0 := by
  rw [Submodule.Quotient.mk_eq_zero]
  exact ⟨(t, 0), by rw [diff_apply]; simp⟩

/-- A section extending to `U₁` has vanishing class in `H1Cok`. -/
lemma h1Cok_mk_resHom_right (t : Γ(X, U₁)) :
    (Submodule.Quotient.mk (X.resHom inf_le_right t) : H1Cok k X U₀ U₁) = 0 := by
  rw [Submodule.Quotient.mk_eq_zero]
  refine ⟨(0, -t), ?_⟩
  rw [diff_apply]
  simp

section Bridge

variable (hcov : U₀ ⊔ U₁ = ⊤)

/-- The two-cover connecting map: the degree-one cohomology class of a section on the
overlap `U₀ ⊓ U₁`, in the cohomology `Sheaf.HModule` of the small Zariski site of `X`. -/
noncomputable def delta :
    Γ(X, U₀ ⊓ U₁) →ₗ[k] Sheaf.HModule (X.moduleKSheaf k) 1 :=
  ((Sheaf.HModule.linearEquivHModule' (isTerminalTop : IsTerminal (⊤ : X.Opens))
      (X.moduleKSheaf k) 1).symm.toLinearMap).comp
    ((X.twoCoverSquare U₀ U₁ hcov).moduleDelta (X.moduleKSheaf k))

/-- The connecting class of a difference of restrictions vanishes. -/
lemma delta_diff (t : Γ(X, U₀) × Γ(X, U₁)) :
    delta k X U₀ U₁ hcov (diff k X U₀ U₁ t) = 0 := by
  have h : (X.twoCoverSquare U₀ U₁ hcov).moduleDelta (X.moduleKSheaf k)
      (diff k X U₀ U₁ t) = 0 :=
    (X.twoCoverSquare U₀ U₁ hcov).moduleDelta_moduleDiff (X.moduleKSheaf k) t
  rw [show delta k X U₀ U₁ hcov (diff k X U₀ U₁ t) =
      (Sheaf.HModule.linearEquivHModule' (isTerminalTop : IsTerminal (⊤ : X.Opens))
          (X.moduleKSheaf k) 1).symm
        ((X.twoCoverSquare U₀ U₁ hcov).moduleDelta (X.moduleKSheaf k)
          (diff k X U₀ U₁ t)) from rfl, h]
  exact map_zero _

/-- The connecting class of a section extending to `U₀` vanishes. -/
lemma delta_resHom_left (t : Γ(X, U₀)) :
    delta k X U₀ U₁ hcov (X.resHom inf_le_left t) = 0 := by
  have h : X.resHom inf_le_left t = diff k X U₀ U₁ (t, 0) := by
    rw [diff_apply]
    simp
  rw [h, delta_diff]

/-- The connecting class of a section extending to `U₁` vanishes. -/
lemma delta_resHom_right (t : Γ(X, U₁)) :
    delta k X U₀ U₁ hcov (X.resHom inf_le_right t) = 0 := by
  have h : X.resHom inf_le_right t = -diff k X U₀ U₁ (0, t) := by
    rw [diff_apply]
    simp
  rw [h, map_neg, delta_diff, neg_zero]

variable (hU₀ : IsAffineOpen U₀) (hU₁ : IsAffineOpen U₁)

include hU₀ hU₁ in
/-- For an affine two-cover, the connecting map is surjective: every degree-one class
comes from a section on the overlap. -/
lemma delta_surjective : Function.Surjective (delta k X U₀ U₁ hcov) := by
  haveI : Subsingleton
      (Sheaf.HModule' (X.moduleKSheaf k) (X.twoCoverSquare U₀ U₁ hcov).X₂ 1) :=
    hU₀.subsingleton_moduleKSheaf_hModule'_one k
  haveI : Subsingleton
      (Sheaf.HModule' (X.moduleKSheaf k) (X.twoCoverSquare U₀ U₁ hcov).X₃ 1) :=
    hU₁.subsingleton_moduleKSheaf_hModule'_one k
  intro y
  obtain ⟨s, hs⟩ := (X.twoCoverSquare U₀ U₁ hcov).moduleDelta_surjective (X.moduleKSheaf k)
    ((Sheaf.HModule.linearEquivHModule' (isTerminalTop : IsTerminal (⊤ : X.Opens))
      (X.moduleKSheaf k) 1) y)
  refine ⟨s, ?_⟩
  rw [show delta k X U₀ U₁ hcov s =
      (Sheaf.HModule.linearEquivHModule' (isTerminalTop : IsTerminal (⊤ : X.Opens))
          (X.moduleKSheaf k) 1).symm
        ((X.twoCoverSquare U₀ U₁ hcov).moduleDelta (X.moduleKSheaf k) s) from rfl, hs,
    LinearEquiv.symm_apply_apply]

/-- **The two-affine-cover H¹ cokernel bridge.** For a scheme `X` over `Spec k` and two
affine opens with `U₀ ⊔ U₁ = ⊤`, the degree-one cohomology of the structure sheaf as a
sheaf of `k`-modules on the small Zariski site of `X` is the cokernel of the
restriction-difference map on sections:
`H¹ₖ(X, 𝒪) ≃ₗ[k] Γ(U₀ ⊓ U₁) ⧸ range((s₀, s₁) ↦ s₀|∩ - s₁|∩)`.
The inverse sends the class of a section on the overlap to its connecting class
(`TwoCover.h1CokEquiv_delta`). -/
noncomputable def h1CokEquiv :
    Sheaf.HModule (X.moduleKSheaf k) 1 ≃ₗ[k] H1Cok k X U₀ U₁ :=
  letI : Subsingleton
      (Sheaf.HModule' (X.moduleKSheaf k) (X.twoCoverSquare U₀ U₁ hcov).X₂ 1) :=
    hU₀.subsingleton_moduleKSheaf_hModule'_one k
  letI : Subsingleton
      (Sheaf.HModule' (X.moduleKSheaf k) (X.twoCoverSquare U₀ U₁ hcov).X₃ 1) :=
    hU₁.subsingleton_moduleKSheaf_hModule'_one k
  (Sheaf.HModule.linearEquivHModule' (isTerminalTop : IsTerminal (⊤ : X.Opens))
      (X.moduleKSheaf k) 1).trans
    ((X.twoCoverSquare U₀ U₁ hcov).h1LinearEquiv (X.moduleKSheaf k)).symm

/-- Compatibility of the bridge with the connecting map: the bridge sends the connecting
class of a section on the overlap to its class in the cokernel. -/
lemma h1CokEquiv_delta (s : Γ(X, U₀ ⊓ U₁)) :
    h1CokEquiv k X U₀ U₁ hcov hU₀ hU₁ (delta k X U₀ U₁ hcov s) =
      Submodule.Quotient.mk s := by
  haveI : Subsingleton
      (Sheaf.HModule' (X.moduleKSheaf k) (X.twoCoverSquare U₀ U₁ hcov).X₂ 1) :=
    hU₀.subsingleton_moduleKSheaf_hModule'_one k
  haveI : Subsingleton
      (Sheaf.HModule' (X.moduleKSheaf k) (X.twoCoverSquare U₀ U₁ hcov).X₃ 1) :=
    hU₁.subsingleton_moduleKSheaf_hModule'_one k
  apply ((X.twoCoverSquare U₀ U₁ hcov).h1LinearEquiv (X.moduleKSheaf k)).injective
  calc ((X.twoCoverSquare U₀ U₁ hcov).h1LinearEquiv (X.moduleKSheaf k))
        (h1CokEquiv k X U₀ U₁ hcov hU₀ hU₁ (delta k X U₀ U₁ hcov s))
      = ((X.twoCoverSquare U₀ U₁ hcov).h1LinearEquiv (X.moduleKSheaf k))
          (((X.twoCoverSquare U₀ U₁ hcov).h1LinearEquiv (X.moduleKSheaf k)).symm
            ((Sheaf.HModule.linearEquivHModule'
                (isTerminalTop : IsTerminal (⊤ : X.Opens)) (X.moduleKSheaf k) 1)
              ((Sheaf.HModule.linearEquivHModule'
                  (isTerminalTop : IsTerminal (⊤ : X.Opens)) (X.moduleKSheaf k) 1).symm
                ((X.twoCoverSquare U₀ U₁ hcov).moduleDelta (X.moduleKSheaf k) s)))) :=
        rfl
    _ = (X.twoCoverSquare U₀ U₁ hcov).moduleDelta (X.moduleKSheaf k) s := by
        rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    _ = ((X.twoCoverSquare U₀ U₁ hcov).h1LinearEquiv (X.moduleKSheaf k))
          (Submodule.Quotient.mk s) :=
        (MayerVietorisSquare.h1LinearEquiv_mk (S := X.twoCoverSquare U₀ U₁ hcov)
          (X.moduleKSheaf k) s).symm

/-- Compatibility of the bridge with the connecting map, inverse form: the inverse
bridge sends the class of a section on the overlap to its connecting class. -/
lemma h1CokEquiv_symm_mk (s : Γ(X, U₀ ⊓ U₁)) :
    (h1CokEquiv k X U₀ U₁ hcov hU₀ hU₁).symm (Submodule.Quotient.mk s) =
      delta k X U₀ U₁ hcov s := by
  apply (h1CokEquiv k X U₀ U₁ hcov hU₀ hU₁).injective
  rw [LinearEquiv.apply_symm_apply, h1CokEquiv_delta]

end Bridge

end TwoCover

end AlgebraicGeometry
