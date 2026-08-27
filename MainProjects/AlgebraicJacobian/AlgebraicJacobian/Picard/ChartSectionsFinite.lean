/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Picard.QuotSupportBaseChange
import AlgebraicJacobian.Picard.SerreTwistSections

/-!
# Chart-local finiteness and the twisted extension / vanishing engine (Serre D1–D3)

This file assembles the chart-local inputs of Serre's finiteness theorem
(`lem:sectionGradedModule_fg`, the deep leaf of `Picard/SerreFiniteness.lean`)
along the Option-B ladder.

## D1 — finite sections on affine charts (Stacks 01PC)

For a finitely presented sheaf of modules `F` on a scheme `X` and an affine
open `U`, the section module `Γ(U, F)` is a **finite** `Γ(U, 𝒪)`-module.  The
all-affine form is already proved upstream as
`Scheme.Modules.module_finite_sections_of_isFinitePresentation`
(`Picard/QuotSupportBaseChange.lean`, step 2 of `lem:proper_support_base_change`).
Here it is packaged in the **chart-local** shape the projective endgame consumes:

* `Scheme.Modules.finite_sections_preimage_of_isAffineHom` — the preimage
  `i ⁻¹ᵁ V` of an affine open `V` under an **affine** morphism `i` (in particular
  a closed immersion) is affine (`IsAffineOpen.preimage`) and carries finite
  `F`-sections.  For a projective `X ↪ ℙ` this is finiteness on the standard
  affine charts `Uᵢ = i⁻¹ D₊(xᵢ)`.
* `Scheme.Hom.IsProjectiveWith.finite_sections_chart` — the projective
  specialisation: finiteness of `F`-sections on the preimage of any affine open
  of the ambient projective space.

## D2 / D3 — twisted extension and vanishing ([Hartshorne] II.5.14, Stacks 01PW)

The geometric heart of Serre finiteness is: for the standard chart `Uᵢ = D(xᵢ)`
of a projective `X` with very ample `L`,

* **(D2, extension)** every `t ∈ Γ(Uᵢ, F)` has `xᵢ^N · t` extending to a global
  section of `F ⊗ L^{⊗N}`;
* **(D3, vanishing)** every `s ∈ Γ(X, F ⊗ L^{⊗m})` whose restriction to `Uᵢ`
  vanishes has `xᵢ^N · s = 0`.

Both statements reduce — after trivialising `L` on the chart, so that the
coordinate section `xᵢ ∈ Γ(X, L)` becomes an ordinary structure-sheaf section
`g ∈ Γ(Uᵢ, 𝒪)` and `F ⊗ L^{⊗N}` becomes `F` there — to the **qcqs
section-localisation engine** of `Picard/QuotScheme.lean`
(`exists_res_eq_pow_smul_of_isCompact`,
`exists_pow_smul_res_eq_zero_of_isCompact`,
`isLocalizedModule_basicOpen_of_isCompact`; Stacks 01P0).  A **projective**
`π : X ⟶ Spec κ` is proper, hence `X` is quasi-compact and quasi-separated
(`Scheme.Hom.IsProjectiveWith.compactSpace`,
`Scheme.Hom.IsProjectiveWith.quasiSeparatedSpace`), so the engine runs on the
whole of `X`.

This file proves the **trivialised (structure-sheaf) form** of D2 / D3 in full,
for an arbitrary quasi-coherent sheaf `G` on a quasi-compact quasi-separated
scheme and a global function `g ∈ Γ(X, ⊤)`:

* `Scheme.Modules.isLocalizedModule_globalSection_of_qcqs` — the master
  localisation: `Γ(X, D(g))` is the localisation `Γ(X, G)[1/g]`;
* `Scheme.Modules.exists_global_res_eq_pow_smul` — the extension half (D2);
* `Scheme.Modules.exists_pow_smul_eq_zero_of_res_eq_zero` — the vanishing half
  (D3).

The remaining bridge to the *un-trivialised* D2 / D3 (identifying `Uᵢ` with the
non-vanishing locus of the invertible section `xᵢ` and absorbing the `L^{⊗N}`
twist) is the coordinate/graded trivialisation dictionary of P0.4
(`serreTwistGluedChartIso`, `IsLocallyTrivial`): the invertible-section analogue
of the localisation engine.  It is documented here as the next step of the
ladder and is *not* used by anything downstream yet.

## References

Blueprint: `lem:sectionGradedModule_fg`
(`blueprint/src/chapters/Picard_QuotScheme.tex`).
Source: [Hartshorne] II.5.14, II.5.17; [Nitsure] §1; Stacks tags 01PC
(finite sections on affines), 01PW / 01P0 (section localisation and the twisted
extension/vanishing).
-/

set_option autoImplicit false

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry

namespace Scheme.Modules

variable {X : Scheme.{u}}

/-! ## D1: finite sections on affine charts (Stacks 01PC) -/

/-- **D1, chart-local form** (Stacks 01PC).  For a finitely presented sheaf of
modules `F` on `X`, an **affine** morphism `i : X ⟶ Y` and an affine open `V` of
`Y`, the section module of `F` over the preimage chart `i ⁻¹ᵁ V` is a finite
`Γ(X, i ⁻¹ᵁ V)`-module.  The preimage of an affine open under an affine morphism
is affine (`IsAffineOpen.preimage`), so this is the all-affine finiteness
`module_finite_sections_of_isFinitePresentation` read on the standard charts of a
closed embedding `X ↪ ℙ`. -/
theorem finite_sections_preimage_of_isAffineHom {Y : Scheme.{u}} (i : X ⟶ Y)
    [IsAffineHom i] (F : X.Modules) [F.IsFinitePresentation] {V : Y.Opens}
    (hV : IsAffineOpen V) :
    Module.Finite Γ(X, i ⁻¹ᵁ V) Γ(F, i ⁻¹ᵁ V) :=
  module_finite_sections_of_isFinitePresentation F ⟨_, hV.preimage i⟩

/-! ## D2 / D3: the qcqs section-localisation engine on a global function -/

/-- **Master global-section localisation** (Stacks 01P0 / 01PW, structure-sheaf
form).  On a quasi-compact quasi-separated scheme `X`, for a quasi-coherent sheaf
`G` and a global function `g ∈ Γ(X, ⊤)`, the basic-open restriction
`Γ(X, G) → Γ(X, D(g))` exhibits `Γ(X, D(g))` as the localisation `Γ(X, G)[1/g]`.
This is the qcqs section-localisation engine `isLocalizedModule_basicOpen_of_isCompact`
instantiated at the (compact, quasi-separated) open `W = ⊤`; it packages both the
extension (D2, `IsLocalizedModule.surj`) and the vanishing (D3,
`IsLocalizedModule.exists_of_eq`) halves. -/
theorem isLocalizedModule_globalSection_of_qcqs [CompactSpace X] [QuasiSeparatedSpace X]
    (G : X.Modules) [G.IsQuasicoherent] (g : Γ(X, ⊤)) :
    letI : Module Γ(X, ⊤) Γ(G, X.basicOpen g) :=
      Module.compHom _ (algebraMap Γ(X, ⊤) Γ(X, X.basicOpen g))
    letI : IsScalarTower Γ(X, ⊤) Γ(X, X.basicOpen g) Γ(G, X.basicOpen g) :=
      IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    IsLocalizedModule (Submonoid.powers g) (restrictBasicOpenₗ G g) := by
  letI : Module Γ(X, ⊤) Γ(G, X.basicOpen g) :=
    Module.compHom _ (algebraMap Γ(X, ⊤) Γ(X, X.basicOpen g))
  letI : IsScalarTower Γ(X, ⊤) Γ(X, X.basicOpen g) Γ(G, X.basicOpen g) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  have hW : IsCompact ((⊤ : X.Opens) : Set X) := by
    rw [TopologicalSpace.Opens.coe_top]; exact isCompact_univ
  have hsep : IsQuasiSeparated ((⊤ : X.Opens) : Set X) := by
    rw [TopologicalSpace.Opens.coe_top]; exact isQuasiSeparated_univ
  exact isLocalizedModule_basicOpen_of_isCompact G hW hsep g

/-- **D2, trivialised extension half** ([Hartshorne] II.5.14 (a), structure-sheaf
form).  On a quasi-compact quasi-separated scheme `X` with quasi-coherent `G` and
`g ∈ Γ(X, ⊤)`, every section `t ∈ Γ(X, D(g))` becomes, after multiplication by a
power `g^n`, the restriction of a **global** section of `G`.  This is the
extension of `t` off the basic open `D(g)` up to the invertibility factor `g^n`,
the trivialised model of "`xᵢ^N · t` extends to `Γ(X, F ⊗ L^{⊗N})`".  The scalar
action of `g^n` on `Γ(X, D(g))` is through the restriction
`Γ(X, ⊤) → Γ(X, D(g))` (the `compHom` module carried in the statement). -/
theorem exists_global_res_eq_pow_smul [CompactSpace X] [QuasiSeparatedSpace X]
    (G : X.Modules) [G.IsQuasicoherent] (g : Γ(X, ⊤)) :
    letI : Module Γ(X, ⊤) Γ(G, X.basicOpen g) :=
      Module.compHom _ (algebraMap Γ(X, ⊤) Γ(X, X.basicOpen g))
    ∀ t : Γ(G, X.basicOpen g), ∃ (s : Γ(G, ⊤)) (n : ℕ),
      G.presheaf.map (homOfLE (X.basicOpen_le g)).op s = g ^ n • t := by
  letI : Module Γ(X, ⊤) Γ(G, X.basicOpen g) :=
    Module.compHom _ (algebraMap Γ(X, ⊤) Γ(X, X.basicOpen g))
  letI : IsScalarTower Γ(X, ⊤) Γ(X, X.basicOpen g) Γ(G, X.basicOpen g) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  haveI := isLocalizedModule_globalSection_of_qcqs G g
  intro t
  obtain ⟨⟨s, c⟩, hc⟩ := IsLocalizedModule.surj (Submonoid.powers g)
    (restrictBasicOpenₗ G g) t
  obtain ⟨n, hn⟩ := c.2
  refine ⟨s, n, ?_⟩
  have hgn : (g : Γ(X, ⊤)) ^ n = (c : Γ(X, ⊤)) := hn
  rw [hgn]
  exact hc.symm

/-- **D3, trivialised vanishing half** ([Hartshorne] II.5.14 (b), structure-sheaf
form).  On a quasi-compact quasi-separated scheme `X` with quasi-coherent `G` and
`g ∈ Γ(X, ⊤)`, a global section `s` whose restriction to the basic open `D(g)`
vanishes is annihilated by a power `g^n`.  This is the trivialised model of
"`s ∈ Γ(X, F ⊗ L^{⊗m})` vanishing on `Uᵢ` has `xᵢ^N · s = 0`"; the scalar action
is the ordinary `Γ(X, ⊤)`-module structure on `Γ(X, G)`. -/
theorem exists_pow_smul_eq_zero_of_res_eq_zero [CompactSpace X] [QuasiSeparatedSpace X]
    (G : X.Modules) [G.IsQuasicoherent] (g : Γ(X, ⊤)) (s : Γ(G, ⊤))
    (hs : G.presheaf.map (homOfLE (X.basicOpen_le g)).op s = 0) :
    ∃ n : ℕ, g ^ n • s = 0 := by
  letI : Module Γ(X, ⊤) Γ(G, X.basicOpen g) :=
    Module.compHom _ (algebraMap Γ(X, ⊤) Γ(X, X.basicOpen g))
  letI : IsScalarTower Γ(X, ⊤) Γ(X, X.basicOpen g) Γ(G, X.basicOpen g) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  haveI := isLocalizedModule_globalSection_of_qcqs G g
  have hs0 : restrictBasicOpenₗ G g s = restrictBasicOpenₗ G g 0 := by
    rw [map_zero]; exact hs
  obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq
    (S := Submonoid.powers g) (f := restrictBasicOpenₗ G g) hs0
  obtain ⟨n, hn⟩ := c.2
  refine ⟨n, ?_⟩
  have hgn : (g : Γ(X, ⊤)) ^ n = (c : Γ(X, ⊤)) := hn
  rw [smul_zero] at hc
  rw [hgn]
  exact hc

end Scheme.Modules

/-! ## Quasi-compactness and quasi-separatedness of a projective total space -/

namespace Scheme.Hom.IsProjectiveWith

variable {X S : Scheme.{0}} {π : X ⟶ S} {L : X.Modules}

/-- **A projective total space over a quasi-compact base is quasi-compact.**
`π` projective is proper (`isProper`), hence quasi-compact, and quasi-compact
morphisms lift compactness from a compact target
(`QuasiCompact.compactSpace_of_compactSpace`).  Over `Spec κ` (a compact affine
scheme) this gives `CompactSpace X`, one half of the qcqs hypothesis feeding the
section-localisation engine on `X`. -/
theorem compactSpace (h : π.IsProjectiveWith L) [CompactSpace S] : CompactSpace X := by
  haveI := h.isProper
  exact QuasiCompact.compactSpace_of_compactSpace π

/-- **A projective total space over a quasi-separated base is quasi-separated.**
`π` projective is proper (`isProper`), hence separated and so quasi-separated, and
quasi-separated morphisms lift quasi-separatedness from a quasi-separated target
(`quasiSeparatedSpace_of_quasiSeparated`).  Over `Spec κ` (an affine, hence
quasi-separated, scheme) this gives `QuasiSeparatedSpace X`, the second half of
the qcqs hypothesis. -/
theorem quasiSeparatedSpace (h : π.IsProjectiveWith L) [QuasiSeparatedSpace S] :
    QuasiSeparatedSpace X := by
  haveI := h.isProper
  exact quasiSeparatedSpace_of_quasiSeparated π

/-- **D1 on the projective charts** (Stacks 01PC).  For a projective `π` carrying
`L`, realised by a closed immersion `i : X ⟶ ℙ(n; S)` for a finite coordinate
type `n`, and a finitely
presented `F`, the section module of `F` over the preimage `i ⁻¹ᵁ V` of any affine
open `V` of the ambient projective space is a finite `Γ(X, i ⁻¹ᵁ V)`-module.  In
particular this applies to the standard coordinate charts `Uᵢ = i ⁻¹ᵁ D₊(xᵢ)`,
which are affine because a closed immersion is an affine morphism.  Existential in
the embedding data (`i`, `n`) recorded by `IsProjectiveWith`. -/
theorem finite_sections_chart (h : π.IsProjectiveWith L) (F : X.Modules)
    [F.IsFinitePresentation] :
    ∃ (n : Type) (_ : Finite n) (i : X ⟶ ℙ(n; S)), IsClosedImmersion i ∧
      i ≫ (ℙ(n; S) ↘ S) = π ∧
      ∀ V : (ℙ(n; S)).Opens, IsAffineOpen V →
        Module.Finite Γ(X, i ⁻¹ᵁ V) Γ(F, i ⁻¹ᵁ V) := by
  obtain ⟨n, hn, i, hi, hcomp, he⟩ := h
  letI : Finite n := hn
  haveI := hi
  exact ⟨n, inferInstance, i, hi, hcomp, fun V hV =>
    Scheme.Modules.finite_sections_preimage_of_isAffineHom i F hV⟩

/-! ## The section-localisation engine on a projective total space -/

/-- **D2 on the projective total space** ([Hartshorne] II.5.14 (a), structure-sheaf
form).  For a projective `π : X ⟶ S` over a quasi-compact quasi-separated base and a
quasi-coherent sheaf `G` on `X`, every section `t ∈ Γ(X, D(g))` over the basic open of
a global function `g ∈ Γ(X, ⊤)` becomes, after multiplication by a power `g^n`, the
restriction of a **global** section of `G`.  `X` is quasi-compact and quasi-separated
because `π` is proper (`compactSpace`, `quasiSeparatedSpace`), so the qcqs
section-localisation engine `Scheme.Modules.exists_global_res_eq_pow_smul` runs
directly on `X`.  This is the trivialised (`L`-untwisted) extension half of D2 on the
projective total space itself; the scalar action of `g^n` on `Γ(X, D(g))` is through
the restriction `Γ(X, ⊤) → Γ(X, D(g))`. -/
theorem exists_global_res_eq_pow_smul [CompactSpace S] [QuasiSeparatedSpace S]
    (h : π.IsProjectiveWith L) (G : X.Modules) [G.IsQuasicoherent] (g : Γ(X, ⊤)) :
    letI : Module Γ(X, ⊤) Γ(G, X.basicOpen g) :=
      Module.compHom _ (algebraMap Γ(X, ⊤) Γ(X, X.basicOpen g))
    ∀ t : Γ(G, X.basicOpen g), ∃ (s : Γ(G, ⊤)) (n : ℕ),
      G.presheaf.map (homOfLE (X.basicOpen_le g)).op s = g ^ n • t := by
  haveI := h.compactSpace
  haveI := h.quasiSeparatedSpace
  exact Scheme.Modules.exists_global_res_eq_pow_smul G g

/-- **D3 on the projective total space** ([Hartshorne] II.5.14 (b), structure-sheaf
form).  For a projective `π : X ⟶ S` over a quasi-compact quasi-separated base and a
quasi-coherent sheaf `G` on `X`, a global section `s` of `G` whose restriction to the
basic open `D(g)` of a global function `g ∈ Γ(X, ⊤)` vanishes is annihilated by a power
`g^n`.  As above `X` is qcqs because `π` is proper, so the qcqs vanishing engine
`Scheme.Modules.exists_pow_smul_eq_zero_of_res_eq_zero` runs directly on `X` — the
trivialised (`L`-untwisted) vanishing half of D3 on the projective total space. -/
theorem exists_pow_smul_eq_zero_of_res_eq_zero [CompactSpace S] [QuasiSeparatedSpace S]
    (h : π.IsProjectiveWith L) (G : X.Modules) [G.IsQuasicoherent]
    (g : Γ(X, ⊤)) (s : Γ(G, ⊤))
    (hs : G.presheaf.map (homOfLE (X.basicOpen_le g)).op s = 0) :
    ∃ n : ℕ, g ^ n • s = 0 := by
  haveI := h.compactSpace
  haveI := h.quasiSeparatedSpace
  exact Scheme.Modules.exists_pow_smul_eq_zero_of_res_eq_zero G g s hs

end Scheme.Hom.IsProjectiveWith

end AlgebraicGeometry
