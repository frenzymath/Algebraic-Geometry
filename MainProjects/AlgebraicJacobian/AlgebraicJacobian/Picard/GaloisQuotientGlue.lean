/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.StableAffineCover

/-!
# Galois quotient gluing, layer 1: the section-level semilinear action (campaign `G2(c)`)

Let `L/K` be a finite Galois extension with group `Γ = Gal(L/K)` and let `X` be a
scheme over `Spec L` with a semilinear `Γ`-action `ρ` (`SemilinearGalAction`).  This
file opens the discharge of the last `G2` gate, `HasGaloisQuotient` (the gluing step
`G2(c)`), with the **overlap audit** (recorded below, before any Lean) and the first
construction layer.  **Update 2026-07-30:** layer 1 turned out to close the gate
outright for an **affine** `X` — `Picard/GaloisQuotientAffineGeneral.lean` uses the
`U = ⊤` instance of the section action below, plus transport along `X.isoSpec`, to get
`hasGaloisQuotient_of_isAffine` as a global instance.  So the layers below are now
needed only for the **non-affine** case (the campaign's glued `J'_r`), and layer 3 may
quote a per-chart quotient instead of constructing one.  The first
construction layer: on every `Γ`-stable open `U` the action transports sections,
making `Γ(X, U)` an `L`-algebra with a semilinear `Γ`-action by ring automorphisms —
the section-level face of `SemilinearGalAction`, i.e. exactly the input format of the
affine quotient theorem `isGaloisQuotient_spec` — together with the scheme-level
restriction `ρ.restrict hU` of the action to `U` and the Spec-functoriality bridge
identifying the restricted action on an affine stable `U` with the `toSpecAut` action
of the section action under `hUa.isoSpec`.

## MANDATORY OPENING AUDIT (milestone 0 — recorded before proving; the overlap pin)

The glue construction needs the overlaps `U ⊓ V` of the stable affine cover to be
manageable.  `U ⊓ V` is always `Γ`-stable and open, but **need not be affine** when
`X` is not separated.  Verdicts on the two pinned resolutions:

* **(a) Stable affine *basic*-open refinement with affine pairwise intersections: NOT
  extractable in general.**  Counterexample genus: the doubled affine plane
  `X = 𝔸²_L ⊔_{𝔸²_L ∖ 0} 𝔸²_L` (base change of the doubled plane over `K`, so it
  carries the canonical semilinear action; each chart is stable and trivially of
  `D(N)`-form, namely `D(1)` in itself).  *Any* two stable affine opens `U₁ ∋ o₁`,
  `U₂ ∋ o₂` around the two origins intersect in an open of `𝔸² ∖ 0` containing a
  punctured neighbourhood `V ∖ 0` of `0`, which is never affine (Hartogs:
  `Γ(V ∖ 0) = Γ(V)` in codimension `2`, so `V ∖ 0 → Spec Γ(V ∖ 0)` is not an open
  immersion at the missing point).  The chart-local identity `D(f) ∩ D(g) = D(fg)`
  is real but only applies *inside a common chart*; two `D(N)`s from different charts
  are exactly the doubled-plane situation.  So (a) is dead **as a route to affine
  overlaps**.

* **However, affineness of the overlaps is NOT required** (this is the audit's main
  finding).  The classical construction (SGA I V.1.8; Mumford AV §7; Milne JV §4
  all state the quotient for orbits-in-affines with **no separatedness hypothesis**)
  handles stable non-affine overlaps via the *local nature of the affine quotient*:
  `π_U : U → Spec (Γ(U)^Γ)` is integral (each `s` kills `∏_γ (T - γ•s)`, a monic
  polynomial over `Γ(U)^Γ`) and its fibres are exactly the `Γ`-orbits (transitivity
  of the action on primes over a prime of the invariants — mathlib:
  `Algebra.IsInvariant` API), so a stable open `V ≤ U` has open image
  `π_U(V) = π_U(V ∖ ∅)` with `π_U⁻¹(π_U V) = V`, and `π_U(V)` is covered by
  invariant basic opens `D(N)`, `N ∈ Γ(U)^Γ` (the `StableAffineCover` norm trick run
  *inside the single chart* `U`, where it needs no separatedness), on which the
  quotient localizes: `(A_N)^Γ = (A^Γ)_N` (kill denominators with the invariant `N`;
  no averaging, so no `|Γ|`-invertibility).  The overlap isos of the glue data then
  come from the uniqueness clause of `isGaloisQuotient_spec` applied on `U ⊓ V`.

* **(b) `[IsSeparated X]` discharge: mathematically true but NOT adopted as the
  pin.**  Separatedness makes `U ⊓ V` a stable affine open, shortcutting the
  image-is-open step; the campaign consumer `J'_r` will indeed be separated
  (`B6`/`J5`).  But the gate `HasGaloisQuotient` is FROZEN without a separatedness
  hypothesis and the honest theorem does not need it, so the pinned route is the
  unconditional one; `(b)` remains the recorded fallback (as a *separate discharge
  theorem* `hasGaloisQuotient_of_isSeparated`, never a strengthening of the frozen
  gate class), to be taken only if the quotient-localization dévissage walls.

**Consequence for the construction plan**: both routes (unconditional and fallback)
consume the *same* layer-1 substrate built here — the section-level semilinear
action on stable opens and its Spec-functoriality.  Layer 2 is now complete:
`GaloisDescent.InvariantQuotientOpen` constructs the quotient-side open of every
stable subopen, identifies its pullback exactly, and proves that it is the actual
open image.  The remaining layers are (3) restriction of the full bundled
`IsGaloisQuotient` to those opens and the resulting `Scheme.GlueData`, and (4) the
glued base-change iso and `T`-points.

**LAYER 2's CONTENT IS NOT THE EQUALITY, and the parenthesis above names the wrong
thing** (`ajc-p3`, 2026-07-30, `I-1461`; landed in
`Picard/GaloisDescent/InvariantsLocalization.lean`, `sorry`-free and axiom-clean
against a live `sorryAx` control).  Read `(A_N)^Γ = (A^Γ)_N` and ask what its
left-hand side means: it presupposes a `Γ`-action on `A_N`, and **there is none**.
Mathlib does not supply it — `exact?` fails on
`MulSemiringAction (L ≃ₐ[K] L) (Localization.Away N)` with `N`'s invariance in
scope — because what is needed is that `γ` maps `Submonoid.powers N` *onto itself*,
which is **false for a general `N`** (`γ` sends `powers N` to `powers (γ • N)`).
That is `SemilinearAction.powers_map_eq`, and it is where invariance of `N` is
spent.

And once the action exists, the equality is **not what layer 3 needs**: layer 3
wants a *quotient* at each piece of a stable cover, not an identification of two
invariant rings.  `SemilinearAction.isSemilinear_away` gives the transported
action's semilinearity, which is exactly the hypothesis of `invariantsSubalgebra`,
`descentAlgHom` and `descentAlgEquiv` — so `isGaloisQuotient_spec` applies verbatim
and `isGaloisQuotient_away` is a *citation* rather than a construction.  That is
the same simplification the 2026-07-30 update above records for the **affine** case
at layer 1 ("layer 3 may quote a per-chart quotient instead of constructing one");
this paragraph carries it to layer 2, which the layer list did not.

So layer 2 is closed: **(a)** the action and its semilinearity landed first;
**(b)** `exists_invariant_basicOpen_le` and `iSup_invariantBasicOpen_eq` give the
invariant-basic-open covering; and **(c)** `GaloisDescent.InvariantQuotientOpen`
constructs the quotient open, proves its exact-preimage identity, and identifies it
with the open image of the stable subopen.  The invariants equality may not be
needed at all, since the per-piece quotient comes from Speiser at the localized ring
directly.  The next layer must prove that restricting the affine quotient to these
opens preserves the full bundled `IsGaloisQuotient`, including its universal
`T`-points clause; that uniqueness statement then supplies the overlap isomorphisms.
Nothing here yet discharges the gate off the affine locus, and the Hironaka trap
still bites at layer 3.

## Main definitions and results (milestone 1)

* `SemilinearGalAction.actApp ρ hU γ : Γ(X, U) ⟶ Γ(X, U)` — transport of sections
  over a `Γ`-stable open along `act γ`, with its calculus (`actApp_one`,
  `actApp_mul`, inverse identities).
* `SemilinearGalAction.sectionsMulSemiringAction` — the induced `Γ`-action by ring
  automorphisms on `Γ(X, U)` (`γ • s = (act γ⁻¹)^♯ s`; a def, not an instance — it
  depends on the stability proof `hU`).  Validated against the affine model: for
  `X = Spec A`, `U = ⊤`, it recovers the ring action (same inversion convention as
  `toSpecAut`).
* `sectionsAlgebraMapHom f U : CommRingCat.of L ⟶ Γ(X, U)` — the structure map on
  sections of a scheme over `Spec L`, with `sectionsAlgebra`/`sectionsAlgebraK` and
  the tower `sections_isScalarTower` (defs, not instances).
* `SemilinearGalAction.actApp_sectionsAlgebraMapHom` — the compat square on
  sections; `isSemilinear_sections` — **the section action is semilinear**
  (`IsSemilinear K L Γ(X, U)`), so the whole `SemilinearAlgebras` engine
  (`invariantsSubalgebra`, `descentAlgEquiv`, `isGaloisQuotient_spec`) applies to
  every stable open.
* `SemilinearGalAction.smul_norm_of_finite` — the norm `∏_γ γ • s` of any section
  over a stable open is `Γ`-invariant (the section-level face of the
  `StableAffineCover` norm trick).
* `SemilinearGalAction.actApp_map` — the restriction map between stable opens is
  `Γ`-equivariant; `isStableOpen_basicOpen`(`_prod_actApp`) — the basic open of an
  invariant section (in particular of any norm) over a stable open is stable.
* `SemilinearGalAction.exists_invariant_basicOpen_le` — **the invariant-basic-open
  covering of layer 2**: every point of a stable open inside a stable affine chart
  has a stable basic-open neighbourhood cut out by an invariant section.
* `SemilinearGalAction.restrict ρ hU : SemilinearGalAction K L U.toScheme (U.ι ≫ f)`
  — the scheme-level restriction of the action to a stable open.
* `SemilinearGalAction.actRes_isoSpec_hom` / `actRes_isoSpec_hom_toSpecAut` —
  **Spec-functoriality**: on an affine stable open, `hUa.isoSpec` intertwines the
  restricted action with `Spec` of the section transport, i.e. with the `toSpecAut`
  action of `sectionsMulSemiringAction`.

Campaign reference: `G2(c)` of `informal/pic-representability-campaign.md`.  Sources:
SGA I V.1.8 and Mumford, *Abelian Varieties* §7 (quotient glued from invariants of
stable affine charts, no separatedness); Milne, *Jacobian Varieties* §4; the affine
heart is Speiser's theorem (`SemilinearAlgebras.descentAlgEquiv`).
-/

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicJacobian.GaloisDescent

/-! ## `appLE`/`resLE` congruence helpers

`Scheme.Hom.appLE`/`resLE` carry a `≤`-proof whose *statement* mentions the
morphism, so rewriting the morphism underneath them needs a congruence lemma (the
`rw` motive is not type-correct otherwise). -/

lemma Scheme.Hom.appLE_congr_hom {Y Z : Scheme.{u}} {g g' : Y ⟶ Z} (e : g = g')
    {V : Z.Opens} {W : Y.Opens} (h : W ≤ g ⁻¹ᵁ V) :
    g.appLE V W h = g'.appLE V W (e ▸ h) := by subst e; rfl

lemma Scheme.Hom.resLE_congr_hom {Y Z : Scheme.{u}} {g g' : Y ⟶ Z} (e : g = g')
    {V : Z.Opens} {W : Y.Opens} (h : W ≤ g ⁻¹ᵁ V) :
    g.resLE V W h = g'.resLE V W (e ▸ h) := by subst e; rfl

namespace SemilinearGalAction

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of L)}

/-! ## Transport of sections along the action, on a stable open -/

section ActApp

variable (ρ : SemilinearGalAction K L X f) {U : X.Opens} (hU : ρ.IsStableOpen U)

/-- Transport of sections over a `Γ`-stable open along `act γ`: the pullback map
`(act γ)^♯` from `Γ(X, U)` to `Γ(X, (act γ)⁻¹ U) = Γ(X, U)`. -/
noncomputable def actApp (γ : L ≃ₐ[K] L) : Γ(X, U) ⟶ Γ(X, U) :=
  (ρ.act γ).hom.appLE U U (hU γ).ge

lemma actApp_one : ρ.actApp hU 1 = 𝟙 Γ(X, U) := by
  rw [actApp, Scheme.Hom.appLE_congr_hom ρ.act_one_hom]
  exact (Scheme.Hom.appLE_eq_app (𝟙 X)).trans (Scheme.Hom.id_app U)

/-- The transport is contravariantly functorial in `γ` (categorical composition
order: `γ` pulls back first). -/
lemma actApp_mul (γ τ : L ≃ₐ[K] L) :
    ρ.actApp hU (γ * τ) = ρ.actApp hU γ ≫ ρ.actApp hU τ := by
  rw [actApp, Scheme.Hom.appLE_congr_hom (ρ.act_mul_hom γ τ)]
  exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm

@[reassoc (attr := simp)]
lemma actApp_actApp_inv (γ : L ≃ₐ[K] L) :
    ρ.actApp hU γ ≫ ρ.actApp hU γ⁻¹ = 𝟙 Γ(X, U) := by
  rw [← actApp_mul, mul_inv_cancel, actApp_one]

@[reassoc (attr := simp)]
lemma actApp_inv_actApp (γ : L ≃ₐ[K] L) :
    ρ.actApp hU γ⁻¹ ≫ ρ.actApp hU γ = 𝟙 Γ(X, U) := by
  rw [← actApp_mul, inv_mul_cancel, actApp_one]

/-- The `Γ`-action by ring automorphisms on the sections over a `Γ`-stable open:
`γ • s = (act γ⁻¹)^♯ s`.  The inversion makes it a **left** action (transport of
sections is contravariant) and matches the affine model: for `X = Spec A`, `U = ⊤`,
`act γ = Spec (γ⁻¹ • ·)` (`toSpecAut`), so `γ • s` recovers the ring action of `γ`.
A def, not an instance — it depends on the stability proof `hU`. -/
@[reducible]
noncomputable def sectionsMulSemiringAction : MulSemiringAction (L ≃ₐ[K] L) Γ(X, U) where
  smul γ s := (ρ.actApp hU γ⁻¹).hom s
  one_smul s := by
    change (ρ.actApp hU 1⁻¹).hom s = s
    rw [inv_one, actApp_one]
    rfl
  mul_smul γ τ s := by
    change (ρ.actApp hU (γ * τ)⁻¹).hom s = (ρ.actApp hU γ⁻¹).hom ((ρ.actApp hU τ⁻¹).hom s)
    rw [mul_inv_rev, actApp_mul]
    rfl
  smul_zero γ := map_zero (ρ.actApp hU γ⁻¹).hom
  smul_add γ s t := map_add (ρ.actApp hU γ⁻¹).hom s t
  smul_one γ := map_one (ρ.actApp hU γ⁻¹).hom
  smul_mul γ s t := map_mul (ρ.actApp hU γ⁻¹).hom s t

lemma sectionsMulSemiringAction_smul_def (γ : L ≃ₐ[K] L) (s : Γ(X, U)) :
    letI := ρ.sectionsMulSemiringAction hU
    γ • s = ρ.actApp hU γ⁻¹ s := rfl

/-- **The norm of a section over a stable open is `Γ`-invariant** (the section-level
face of the `StableAffineCover` norm trick): for any `s : Γ(X, U)`,
`τ • ∏_γ γ • s = ∏_γ γ • s`.  Feeds the invariant-basic-open covering of stable
opens inside a chart (glue layer 2). -/
lemma smul_norm_of_finite [FiniteDimensional K L] (s : Γ(X, U)) (τ : L ≃ₐ[K] L) :
    letI := ρ.sectionsMulSemiringAction hU
    τ • (∏ γ : L ≃ₐ[K] L, γ • s) = ∏ γ : L ≃ₐ[K] L, γ • s := by
  letI := ρ.sectionsMulSemiringAction hU
  have h : τ • (∏ γ : L ≃ₐ[K] L, γ • s) = ∏ γ : L ≃ₐ[K] L, τ • (γ • s) :=
    map_prod (MulSemiringAction.toRingHom (L ≃ₐ[K] L) Γ(X, U) τ) _ _
  rw [h, Finset.prod_congr rfl fun γ _ => (mul_smul τ γ s).symm]
  exact Fintype.prod_equiv (Equiv.mulLeft τ) _ _ fun γ => rfl

/-- Naturality of the section transport in the stable open: transporting then
restricting between two stable opens is restricting then transporting.  (In
particular the restriction map between stable opens is `Γ`-equivariant for the
section actions, hence maps invariants to invariants — the map that glue layer 2
localizes.) -/
lemma actApp_map {V : X.Opens} (hV : ρ.IsStableOpen V) (hVU : V ≤ U)
    (γ : L ≃ₐ[K] L) :
    ρ.actApp hU γ ≫ X.presheaf.map (homOfLE hVU).op
      = X.presheaf.map (homOfLE hVU).op ≫ ρ.actApp hV γ := by
  rw [actApp, actApp, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

/-- Pulling back a basic open by the action is the basic open of the transported
section.  This is the pointwise bridge between orbit containment and the norm
construction in `exists_invariant_basicOpen_le`. -/
lemma preimage_basicOpen_actApp (γ : L ≃ₐ[K] L) (s : Γ(X, U)) :
    (ρ.act γ).hom ⁻¹ᵁ X.basicOpen s = X.basicOpen (ρ.actApp hU γ s) := by
  have h1 : ρ.actApp hU γ s
      = X.presheaf.map (homOfLE (hU γ).ge).op ((ρ.act γ).hom.app U s) := rfl
  have hle : X.basicOpen ((ρ.act γ).hom.app U s) ≤ U :=
    (X.basicOpen_le _).trans_eq (hU γ)
  calc
    (ρ.act γ).hom ⁻¹ᵁ X.basicOpen s
        = X.basicOpen ((ρ.act γ).hom.app U s) := Scheme.preimage_basicOpen _ _
    _ = U ⊓ X.basicOpen ((ρ.act γ).hom.app U s) := (inf_eq_right.mpr hle).symm
    _ = X.basicOpen (ρ.actApp hU γ s) := by rw [h1, Scheme.basicOpen_res]

/-- **The basic open of an invariant section over a stable open is stable.**  The
invariance hypothesis is pinned inverse-free through the transport `actApp` (for the
section action it reads `γ • N = N` for all `γ`).  Together with
`smul_norm_of_finite`/`isStableOpen_basicOpen_prod_actApp` this is the
invariant-basic-open covering machine of glue layer 2. -/
lemma isStableOpen_basicOpen {N : Γ(X, U)}
    (hN : ∀ γ : L ≃ₐ[K] L, ρ.actApp hU γ N = N) :
    ρ.IsStableOpen (X.basicOpen N) := by
  intro γ
  have h1 : ρ.actApp hU γ N
      = X.presheaf.map (homOfLE (hU γ).ge).op ((ρ.act γ).hom.app U N) := rfl
  have hle : X.basicOpen ((ρ.act γ).hom.app U N) ≤ U :=
    (X.basicOpen_le _).trans_eq (hU γ)
  calc (ρ.act γ).hom ⁻¹ᵁ X.basicOpen N
      = X.basicOpen ((ρ.act γ).hom.app U N) := Scheme.preimage_basicOpen _ _
    _ = U ⊓ X.basicOpen ((ρ.act γ).hom.app U N) := (inf_eq_right.mpr hle).symm
    _ = X.basicOpen (ρ.actApp hU γ N) := by rw [h1, Scheme.basicOpen_res]
    _ = X.basicOpen N := by rw [hN γ]

/-- The basic open of a section invariant for `sectionsMulSemiringAction` is stable.
This is the action-shaped form consumed by localization at the invariant section. -/
lemma isStableOpen_basicOpen_of_smul_eq (N : Γ(X, U)) :
    letI := ρ.sectionsMulSemiringAction hU
    (∀ γ : L ≃ₐ[K] L, γ • N = N) → ρ.IsStableOpen (X.basicOpen N) := by
  letI := ρ.sectionsMulSemiringAction hU
  intro hN
  apply ρ.isStableOpen_basicOpen hU
  intro γ
  have h := hN γ⁻¹
  change ρ.actApp hU γ N = N
  simpa [sectionsMulSemiringAction_smul_def] using h

/-- The basic open of the **norm** `∏_γ (act γ)^♯ s` of *any* section over a stable
open is stable — the section-level norm trick, transport form. -/
lemma isStableOpen_basicOpen_prod_actApp [FiniteDimensional K L] (s : Γ(X, U)) :
    ρ.IsStableOpen (X.basicOpen (∏ γ : L ≃ₐ[K] L, ρ.actApp hU γ s)) := by
  refine ρ.isStableOpen_basicOpen hU fun τ => ?_
  have h : ρ.actApp hU τ (∏ γ : L ≃ₐ[K] L, ρ.actApp hU γ s)
      = ∏ γ : L ≃ₐ[K] L, ρ.actApp hU τ (ρ.actApp hU γ s) :=
    map_prod (ρ.actApp hU τ).hom _ _
  have h2 : ∀ γ : L ≃ₐ[K] L,
      ρ.actApp hU τ (ρ.actApp hU γ s) = ρ.actApp hU (γ * τ) s := by
    intro γ
    rw [actApp_mul]
    rfl
  rw [h, Finset.prod_congr rfl fun γ _ => h2 γ]
  exact Fintype.prod_equiv (Equiv.mulRight τ) _ _ fun γ => rfl

/-- **Invariant-basic-open covering inside one stable affine chart** (quotient-glue
layer 2): if `V ≤ U` is stable and `U` is affine and stable, then every point of
`V` lies in a basic open `D(N) ≤ V` cut out by an invariant section of `U`.

The section `N` is the norm of a prime-avoidance section containing the orbit of
the point.  Thus the theorem uses only the stable affine chart already supplied by
`HasStableAffineCover`; it adds no separatedness or quasi-projectivity assumption.
The returned stability proof lets the localized affine quotient be applied directly
on `D(N)`. -/
theorem exists_invariant_basicOpen_le [FiniteDimensional K L]
    (hUa : IsAffineOpen U) {V : X.Opens} (hVU : V ≤ U)
    (hV : ρ.IsStableOpen V) {x : X} (hx : x ∈ V) :
    letI := ρ.sectionsMulSemiringAction hU
    ∃ N : Γ(X, U), (∀ γ : L ≃ₐ[K] L, γ • N = N) ∧
      x ∈ X.basicOpen N ∧ X.basicOpen N ≤ V ∧ ρ.IsStableOpen (X.basicOpen N) := by
  classical
  letI := ρ.sectionsMulSemiringAction hU
  obtain ⟨s, hs_mem, hs_le⟩ := exists_basicOpen_le_of_finite hUa
    (fun γ : L ≃ₐ[K] L => (ρ.act γ).hom.base x)
    (fun γ => by
      apply hVU
      change x ∈ (ρ.act γ).hom ⁻¹ᵁ V
      rw [hV γ]
      exact hx)
    (fun γ => by
      change x ∈ (ρ.act γ).hom ⁻¹ᵁ V
      rw [hV γ]
      exact hx)
  let N : Γ(X, U) := ∏ γ : L ≃ₐ[K] L, γ • s
  have hN : ∀ τ : L ≃ₐ[K] L, τ • N = N :=
    fun τ => ρ.smul_norm_of_finite hU s τ
  have hbo : X.basicOpen N =
      Finset.univ.inf fun γ : L ≃ₐ[K] L => X.basicOpen (γ • s) := by
    exact basicOpen_finset_prod ⟨1, Finset.mem_univ 1⟩ _
  refine ⟨N, hN, ?_, ?_, ρ.isStableOpen_basicOpen_of_smul_eq hU N hN⟩
  · rw [hbo, mem_finset_inf]
    intro γ _
    rw [sectionsMulSemiringAction_smul_def, ← ρ.preimage_basicOpen_actApp hU]
    exact hs_mem γ⁻¹
  · rw [hbo]
    have hle := Finset.inf_le
      (s := Finset.univ)
      (f := fun γ : L ≃ₐ[K] L => X.basicOpen (γ • s))
      (Finset.mem_univ (1 : L ≃ₐ[K] L))
    have hs_le' : X.basicOpen ((1 : L ≃ₐ[K] L) • s) ≤ V := by
      simpa using hs_le
    exact hle.trans hs_le'

/-- Invariant basic opens of the stable affine chart `U` which are contained in
`V`.  This is the index type used by the quotient-chart cover in layer 3. -/
def InvariantBasicOpenIndex (V : X.Opens) : Type u :=
  letI := ρ.sectionsMulSemiringAction hU
  {N : Γ(X, U) // (∀ γ : L ≃ₐ[K] L, γ • N = N) ∧ X.basicOpen N ≤ V}

/-- Every member of `InvariantBasicOpenIndex` cuts out a stable open. -/
lemma invariantBasicOpen_isStable {V : X.Opens}
    (i : InvariantBasicOpenIndex ρ hU V) :
    ρ.IsStableOpen (X.basicOpen i.1) := by
  letI := ρ.sectionsMulSemiringAction hU
  exact ρ.isStableOpen_basicOpen_of_smul_eq hU i.1 i.2.1

/-- **The invariant basic opens contained in a stable subopen cover it.**  This is
the lattice form of `exists_invariant_basicOpen_le`, ready for `OpenCover` and
`Scheme.GlueData`: the point-indexed existence theorem has been assembled into the
exact supremum identity required by gluing. -/
theorem iSup_invariantBasicOpen_eq [FiniteDimensional K L]
    (hUa : IsAffineOpen U) {V : X.Opens} (hVU : V ≤ U)
    (hV : ρ.IsStableOpen V) :
    (⨆ i : InvariantBasicOpenIndex ρ hU V, X.basicOpen i.1) = V := by
  apply le_antisymm
  · exact iSup_le fun i => i.2.2
  · intro x hx
    obtain ⟨N, hN, hxN, hNV, -⟩ :=
      ρ.exists_invariant_basicOpen_le hU hUa hVU hV hx
    rw [TopologicalSpace.Opens.mem_iSup]
    exact ⟨⟨N, hN, hNV⟩, hxN⟩

end ActApp

/-! ## The structure map on sections of a scheme over `Spec L` -/

section SectionsAlgebra

variable (f) (U : X.Opens)

/-- The structure map on sections: for a scheme `f : X ⟶ Spec L` and any open `U`,
the composite `L ≅ Γ(Spec L, ⊤) ⟶ Γ(X, ⊤) ⟶ Γ(X, U)`. -/
noncomputable def sectionsAlgebraMapHom : CommRingCat.of L ⟶ Γ(X, U) :=
  (Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ f.appLE ⊤ U le_top

/-- The `L`-algebra structure on the sections of a scheme over `Spec L` (a def, not
an instance — introduce it with `letI` where needed). -/
@[reducible]
noncomputable def sectionsAlgebra : Algebra L Γ(X, U) :=
  (sectionsAlgebraMapHom f U).hom.toAlgebra

/-- The `K`-algebra structure on the sections of a scheme over `Spec L`, through
`K → L` (a def, not an instance). -/
@[reducible]
noncomputable def sectionsAlgebraK : Algebra K Γ(X, U) :=
  ((sectionsAlgebraMapHom f U).hom.comp (algebraMap K L)).toAlgebra

lemma sections_isScalarTower :
    letI := sectionsAlgebra f U
    letI := sectionsAlgebraK (K := K) f U
    IsScalarTower K L Γ(X, U) := by
  letI := sectionsAlgebra f U
  letI := sectionsAlgebraK (K := K) f U
  exact IsScalarTower.of_algebraMap_eq fun k => rfl

end SectionsAlgebra

/-! ## Semilinearity of the section action -/

section Semilinearity

variable (ρ : SemilinearGalAction K L X f) {U : X.Opens} (hU : ρ.IsStableOpen U)

/-- The compatibility square of a semilinear action, on sections over a stable open:
transporting the structure map along `act γ` twists it by `γ⁻¹` (the same inversion
as `toSpecAut`, forced by contravariance of taking sections). -/
lemma actApp_sectionsAlgebraMapHom (γ : L ≃ₐ[K] L) :
    sectionsAlgebraMapHom f U ≫ ρ.actApp hU γ
      = CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[K] L) L γ⁻¹)
          ≫ sectionsAlgebraMapHom f U := by
  rw [sectionsAlgebraMapHom, actApp, Category.assoc,
    Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_congr_hom (ρ.compat γ),
    Scheme.Hom.appLE_congr_hom
      (congrArg (f ≫ ·) (toSpecAut_hom (L ≃ₐ[K] L) L γ)),
    Scheme.Hom.comp_appLE, ← Category.assoc, ← Category.assoc]
  congr 1
  exact (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[K] L) L γ⁻¹))).symm

/-- **The section action on a stable open is semilinear** over the Galois action on
`L`: with the (`letI`) instances `sectionsMulSemiringAction` and `sectionsAlgebra`,
`Γ(X, U)` is an `L`-algebra with semilinear `Γ`-action by ring automorphisms — the
exact input format of the affine quotient engine
(`invariantsSubalgebra`/`descentAlgEquiv`/`isGaloisQuotient_spec`). -/
theorem isSemilinear_sections :
    letI := ρ.sectionsMulSemiringAction hU
    letI := sectionsAlgebra f U
    IsSemilinear K L Γ(X, U) := by
  letI := ρ.sectionsMulSemiringAction hU
  letI := sectionsAlgebra f U
  refine SemilinearAction.isSemilinear_of_smul_algebraMap K L Γ(X, U) fun γ a => ?_
  change (ρ.actApp hU γ⁻¹).hom ((sectionsAlgebraMapHom f U).hom a)
    = (sectionsAlgebraMapHom f U).hom (γ a)
  have h := congrArg (fun m => CommRingCat.Hom.hom m a)
    (ρ.actApp_sectionsAlgebraMapHom hU γ⁻¹)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
  rw [h]
  -- `(γ⁻¹)⁻¹ • a = γ a`: `inv_inv` is definitional for `AlgEquiv` (structure eta)
  congr 1

end Semilinearity

/-! ## Restriction of the action to a stable open, and Spec-functoriality -/

section Restrict

variable (ρ : SemilinearGalAction K L X f) {U : X.Opens} (hU : ρ.IsStableOpen U)

/-- The endomorphism of `U.toScheme` induced by `act γ` on a `Γ`-stable open. -/
noncomputable def actRes (γ : L ≃ₐ[K] L) : U.toScheme ⟶ U.toScheme :=
  (ρ.act γ).hom.resLE U U (hU γ).ge

@[reassoc (attr := simp)]
lemma actRes_ι (γ : L ≃ₐ[K] L) :
    ρ.actRes hU γ ≫ U.ι = U.ι ≫ (ρ.act γ).hom :=
  Scheme.Hom.resLE_comp_ι _ _

lemma actRes_one : ρ.actRes hU 1 = 𝟙 U.toScheme := by
  rw [actRes, Scheme.Hom.resLE_congr_hom ρ.act_one_hom, Scheme.Hom.resLE_id]
  exact Scheme.homOfLE_rfl X U

/-- The scheme-level restriction is contravariantly functorial in the categorical
order (`(act (γτ))|_U = (act τ)|_U ≫ (act γ)|_U`, matching `act_mul_hom`). -/
lemma actRes_mul (γ τ : L ≃ₐ[K] L) :
    ρ.actRes hU (γ * τ) = ρ.actRes hU τ ≫ ρ.actRes hU γ := by
  rw [actRes, Scheme.Hom.resLE_congr_hom (ρ.act_mul_hom γ τ)]
  exact (Scheme.Hom.resLE_comp_resLE _ _ _ _).symm

@[reassoc (attr := simp)]
lemma actRes_actRes_inv (γ : L ≃ₐ[K] L) :
    ρ.actRes hU γ ≫ ρ.actRes hU γ⁻¹ = 𝟙 U.toScheme := by
  rw [← actRes_mul, inv_mul_cancel, actRes_one]

@[reassoc (attr := simp)]
lemma actRes_inv_actRes (γ : L ≃ₐ[K] L) :
    ρ.actRes hU γ⁻¹ ≫ ρ.actRes hU γ = 𝟙 U.toScheme := by
  rw [← actRes_mul, mul_inv_cancel, actRes_one]

/-- **The restriction of a semilinear Galois action to a `Γ`-stable open**, as a
semilinear action on `U.toScheme` over `U.ι ≫ f`.  This is the per-chart input of
the glue construction: for a stable *affine* `U` it is identified with the affine
model on `Spec Γ(X, U)` by `actRes_isoSpec_hom_toSpecAut` below. -/
noncomputable def restrict : SemilinearGalAction K L U.toScheme (U.ι ≫ f) where
  act := MonoidHom.mk'
    (fun γ =>
      { hom := ρ.actRes hU γ
        inv := ρ.actRes hU γ⁻¹
        hom_inv_id := ρ.actRes_actRes_inv hU γ
        inv_hom_id := ρ.actRes_inv_actRes hU γ })
    (fun γ τ => by
      refine Iso.ext ?_
      change ρ.actRes hU (γ * τ) = ρ.actRes hU τ ≫ ρ.actRes hU γ
      exact ρ.actRes_mul hU γ τ)
  compat γ := by
    change ρ.actRes hU γ ≫ (U.ι ≫ f) = (U.ι ≫ f) ≫ (toSpecAut (L ≃ₐ[K] L) L γ).hom
    rw [← Category.assoc, actRes_ι, Category.assoc, ρ.compat γ, Category.assoc]

@[simp] lemma restrict_act_hom (γ : L ≃ₐ[K] L) :
    ((ρ.restrict hU).act γ).hom = ρ.actRes hU γ := rfl

/-- **Spec-functoriality of the section transport** (milestone 1, bridge to the
affine engine): on an affine `Γ`-stable open, `hUa.isoSpec` intertwines the
restricted action morphism `act γ |_U` with `Spec` of the section transport
`actApp γ`. -/
theorem actRes_isoSpec_hom (hUa : IsAffineOpen U) (γ : L ≃ₐ[K] L) :
    ρ.actRes hU γ ≫ hUa.isoSpec.hom = hUa.isoSpec.hom ≫ Spec.map (ρ.actApp hU γ) := by
  haveI : IsAffine U.toScheme := hUa
  have hiso : hUa.isoSpec.hom = U.toScheme.isoSpec.hom ≫ Spec.map U.topIso.inv := rfl
  rw [hiso, ← Category.assoc, ← Scheme.isoSpec_hom_naturality (ρ.actRes hU γ),
    Category.assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  have happ : (ρ.actRes hU γ).appTop
      = U.topIso.hom ≫ ρ.actApp hU γ ≫ U.topIso.inv :=
    Scheme.Hom.resLE_app_top _ _
  rw [happ, ← Category.assoc, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Spec-functoriality, `toSpecAut` form: on an affine `Γ`-stable open the
restricted action corresponds under `isoSpec` to the affine-model action
`toSpecAut` of the section action `sectionsMulSemiringAction` on `Spec Γ(X, U)` —
i.e. `hUa.isoSpec.hom` is equivariant.  (Bundling this as
`SemilinearGalAction.IsEquivariant` of `ρ.restrict hU` against
`specSemilinearGalAction` is glue layer 3, where the `letI` algebra instances are
assembled.) -/
theorem actRes_isoSpec_hom_toSpecAut (hUa : IsAffineOpen U) (γ : L ≃ₐ[K] L) :
    letI := ρ.sectionsMulSemiringAction hU
    ((ρ.restrict hU).act γ).hom ≫ hUa.isoSpec.hom
      = hUa.isoSpec.hom ≫ (toSpecAut (L ≃ₐ[K] L) Γ(X, U) γ).hom := by
  letI := ρ.sectionsMulSemiringAction hU
  rw [restrict_act_hom, toSpecAut_hom]
  have hhom : CommRingCat.ofHom
      (MulSemiringAction.toRingHom (L ≃ₐ[K] L) Γ(X, U) γ⁻¹) = ρ.actApp hU γ := by
    refine CommRingCat.hom_ext (RingHom.ext fun s => ?_)
    change (ρ.actApp hU (γ⁻¹)⁻¹).hom s = (ρ.actApp hU γ).hom s
    rw [inv_inv]
  rw [hhom]
  exact ρ.actRes_isoSpec_hom hU hUa γ

end Restrict

end SemilinearGalAction

end AlgebraicJacobian.GaloisDescent
