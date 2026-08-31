/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyZarMap

/-!
# The locally certified divisor vehicle is a Zariski sheaf on the slice (DD-2 S6a)

The sheaf condition of the locally certified vehicle `divFamZar` for *arbitrary*
Zariski open covers of *arbitrary* tests in `Over (Spec k)` — the separation and
gluing halves, lifted from the affine basic-open S5b keystones
(`AlgebraicJacobian.Picard.DivisorFamilyZarMapAlg` / `…ZarGlue`) through the
affine-opens limit.  This is the `Pic0ZariskiSheaf` mirror on the Addendum-2 carrier
(`informal/spec-dd-2.md` §6), in the form the DD-R lane's `divRep` restatement
consumes.

## Separation

* `AlgebraicGeometry.divFamZar.ext_of_le_cover`: two sections of `divFamZar C π n T`
  agreeing on every affine open subordinate to an open cover of `T.left` agree.

## Gluing

* `AlgebraicGeometry.divFamZar.LocalData`: compatible local data on an open cover —
  a locally certified class at every affine open subordinate to a cover member,
  restricting correctly within a member (`res`) and agreeing across members on shared
  affine opens (`glue`).
* `AlgebraicGeometry.divFamZar.IsGlueValue`: the characterizing property of the value
  at an affine open of a section glued from compatible local data.  Values are unique
  (`glueValue_unique`) and exist (`exists_isGlueValue`).
* `AlgebraicGeometry.divFamZar.existsUnique_glue_of_le_cover`: **the gluing half** —
  a family of local sections on an open cover, compatible on the affine overlaps,
  glues to a unique section of `divFamZar C π n T`.
-/

set_option autoImplicit false
/- Statements mix the section rings `Γ(T.left, ·)` with the locally certified
divisor-functor values over them, which are stated on the product spelling
`(C ⊗ overSpec k R).left`; see `AlgebraicJacobian.Cohomology.RelativeSectionsLinear`. -/
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161), so the pinned synthesis
depth must be set in-file for the faithful per-file check. -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] Over.sectionsAlgebra Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {π : C.left ⟶ P1 k} [IsAffineHom π] {n : ℕ}

namespace divFamZar

/-! ## Separation -/

/-- **Separation of the locally certified vehicle** (`informal/spec-dd-2.md` §6,
Addendum 2 — the `picEt.ext_of_le_cover` mirror): two sections of `divFamZar C π n T`
agreeing on every affine open subordinate to an open cover of `T.left` are equal — the
separation half of the Zariski sheaf property at an arbitrary test. -/
theorem ext_of_le_cover {T : Over (Spec (.of k))} {ι' : Type*}
    (O : ι' → T.left.Opens) (hcov : ∀ p : T.left, ∃ i, p ∈ O i)
    {s t : divFamZar C π n T}
    (h : ∀ (U : T.left.affineOpens) (i : ι'), U.1 ≤ O i → s.1 U = t.1 U) : s = t := by
  classical
  refine ext fun U => ?_
  obtain ⟨sub, hspan, hsub⟩ := Scheme.exists_basic_subcover U.2
    (fun U₀ => ∃ i, U₀ ≤ O i)
    (fun w _ => by
      obtain ⟨i, hi⟩ := hcov w
      exact ⟨O i, hi, ⟨i, le_rfl⟩⟩)
  refine eq_of_basic_eq U sub hspan (fun r hr => ?_)
  obtain ⟨U₀, ⟨i, hle⟩, hrle⟩ := hsub r hr
  rw [s.compat ⟨_, U.2.basicOpen r⟩ U (T.left.basicOpen_le r),
    t.compat ⟨_, U.2.basicOpen r⟩ U (T.left.basicOpen_le r)]
  exact h ⟨T.left.basicOpen r, U.2.basicOpen r⟩ i (hrle.trans hle)

/-! ## Local data on an open cover -/

variable {T : Over (Spec (.of k))} {ι : Type u} (O : ι → T.left.Opens)

/-- **Compatible local data** on an open cover `O` of `T.left`: a locally certified
class at every affine open subordinate to a cover member, restricting correctly within
a member (`res`) and agreeing across members on shared affine opens (`glue`).  This is
the input of the gluing half — the vehicle-native spelling of a compatible family of
local sections of `divFamZar` over the cover. -/
structure LocalData (v : ∀ (i : ι) (W : T.left.affineOpens), W.1 ≤ O i →
    DivFamZar C Γ(T.left, W.1) π n) : Prop where
  res : ∀ (i : ι) (W W' : T.left.affineOpens) (hW : W.1 ≤ O i) (hW' : W'.1 ≤ O i)
    (h : W.1 ≤ W'.1),
      DivFamZar.mapAlgHom (Over.resAlgHom T h) (v i W' hW') = v i W hW
  glue : ∀ (i j : ι) (W : T.left.affineOpens) (hi : W.1 ≤ O i) (hj : W.1 ≤ O j),
      v i W hi = v j W hj

variable (v : ∀ (i : ι) (W : T.left.affineOpens), W.1 ≤ O i →
  DivFamZar C Γ(T.left, W.1) π n)

/-- The characterizing property of the glued value at `W`: on every affine sub-open of
`W` contained in a cover member, it restricts to the local datum there. -/
def IsGlueValue (W : T.left.affineOpens) (z : DivFamZar C Γ(T.left, W.1) π n) : Prop :=
  ∀ (W₀ : T.left.affineOpens) (hW₀ : W₀.1 ≤ W.1) (i : ι) (hi : W₀.1 ≤ O i),
    DivFamZar.mapAlgHom (Over.resAlgHom T hW₀) z = v i W₀ hi

variable {O v}

/-- Glued values are unique — from the Zariski separation over a basic refinement
subordinate to the cover. -/
theorem glueValue_unique (hcov : ∀ p : T.left, ∃ i, p ∈ O i)
    {W : T.left.affineOpens} {z z' : DivFamZar C Γ(T.left, W.1) π n}
    (hz : IsGlueValue O v W z) (hz' : IsGlueValue O v W z') : z = z' := by
  classical
  obtain ⟨sub, hspan, hsub⟩ := Scheme.exists_basic_subcover W.2
    (fun U₀ => ∃ i, U₀ ≤ O i)
    (fun w _ => by obtain ⟨i, hi⟩ := hcov w; exact ⟨O i, hi, ⟨i, le_rfl⟩⟩)
  refine eq_of_basic_eq W sub hspan (fun r hr => ?_)
  obtain ⟨U₀, ⟨i, hi⟩, hle⟩ := hsub r hr
  rw [hz ⟨_, W.2.basicOpen r⟩ (T.left.basicOpen_le r) i (hle.trans hi),
    hz' ⟨_, W.2.basicOpen r⟩ (T.left.basicOpen_le r) i (hle.trans hi)]

set_option maxHeartbeats 1600000 in
-- The instance towers over the section rings of the basic refinement exceed the
-- default elaboration budget (as in `Pic0ZariskiSheaf.exists_isGlueValue`).
/-- **Existence of the glued value**: compatible local data on an open cover has a
value at every affine open of `T.left`, glued over a finite basic-open refinement
subordinate to the cover — the S5b gluing keystone through
`divFamZar.exists_glue_of_basic_compat`. -/
theorem exists_isGlueValue (hcov : ∀ p : T.left, ∃ i, p ∈ O i)
    (hv : LocalData O v) (W : T.left.affineOpens) :
    ∃ z, IsGlueValue O v W z := by
  classical
  -- the basic refinement subordinate to the cover
  obtain ⟨sub, hspan, hsub⟩ := Scheme.exists_basic_subcover W.2
    (fun U₀ => ∃ i, U₀ ≤ O i)
    (fun w _ => by obtain ⟨i, hi⟩ := hcov w; exact ⟨O i, hi, ⟨i, le_rfl⟩⟩)
  have hsub' : ∀ r ∈ sub, ∃ i, T.left.basicOpen r ≤ O i := fun r hr => by
    obtain ⟨U₀, ⟨i, hi⟩, hle⟩ := hsub r hr
    exact ⟨i, hle.trans hi⟩
  choose ic hic using hsub'
  have hbmul : ∀ r r' : ↥sub,
      T.left.basicOpen ((r : Γ(T.left, W.1)) * (r' : Γ(T.left, W.1)))
        ≤ T.left.basicOpen (r : Γ(T.left, W.1)) := fun r r' => by
    rw [Scheme.basicOpen_mul]
    exact inf_le_left
  have hbmul' : ∀ r r' : ↥sub,
      T.left.basicOpen ((r : Γ(T.left, W.1)) * (r' : Γ(T.left, W.1)))
        ≤ T.left.basicOpen (r' : Γ(T.left, W.1)) := fun r r' => by
    rw [Scheme.basicOpen_mul]
    exact inf_le_right
  -- glue the local pieces over the basic refinement
  obtain ⟨z, hz⟩ := exists_glue_of_basic_compat W sub hspan
    (fun r : ↥sub => v (ic r.1 r.2) ⟨_, W.2.basicOpen r.1⟩ (hic r.1 r.2))
    hbmul hbmul'
    (fun r r' => by
      -- the overlap compatibility, from `res` and `glue`
      rw [hv.res (ic r.1 r.2) ⟨_, W.2.basicOpen (r.1 * r'.1)⟩ ⟨_, W.2.basicOpen r.1⟩
          ((hbmul r r').trans (hic r.1 r.2)) (hic r.1 r.2) (hbmul r r'),
        hv.res (ic r'.1 r'.2) ⟨_, W.2.basicOpen (r.1 * r'.1)⟩ ⟨_, W.2.basicOpen r'.1⟩
          ((hbmul' r r').trans (hic r'.1 r'.2)) (hic r'.1 r'.2) (hbmul' r r')]
      exact hv.glue (ic r.1 r.2) (ic r'.1 r'.2) ⟨_, W.2.basicOpen (r.1 * r'.1)⟩
        ((hbmul r r').trans (hic r.1 r.2)) ((hbmul' r r').trans (hic r'.1 r'.2)))
  -- the glued value has the characterizing property
  refine ⟨z, fun W₀ hW₀ i hi => ?_⟩
  obtain ⟨sub₀, hspan₀, hsub₀⟩ := Scheme.exists_basic_subcover W₀.2
    (fun U₀ => ∃ r ∈ sub, U₀ = T.left.basicOpen r)
    (fun w hw => by
      have hwW : w ∈ (⨆ r ∈ (↑sub : Set Γ(T.left, W.1)), T.left.basicOpen r) := by
        rw [iSup_basicOpen_of_span_eq_top _ _ hspan]
        exact hW₀ hw
      obtain ⟨r, hr⟩ := Opens.mem_iSup.mp hwW
      obtain ⟨hrsub, hwr⟩ := Opens.mem_iSup.mp hr
      exact ⟨T.left.basicOpen r, hwr, ⟨r, hrsub, rfl⟩⟩)
  refine eq_of_basic_eq W₀ sub₀ hspan₀ (fun q hq => ?_)
  obtain ⟨U₀, ⟨r, hr, rfl⟩, hqle⟩ := hsub₀ q hq
  -- the left side restricts through the glued datum
  have hzr : DivFamZar.mapAlgHom (Over.resAlgHom T (T.left.basicOpen_le r)) z
      = v (ic r hr) ⟨_, W.2.basicOpen r⟩ (hic r hr) := hz ⟨r, hr⟩
  have hL : DivFamZar.mapAlgHom (Over.resAlgHom T (T.left.basicOpen_le q))
      (DivFamZar.mapAlgHom (Over.resAlgHom T hW₀) z)
      = v (ic r hr) ⟨_, W₀.2.basicOpen q⟩ (hqle.trans (hic r hr)) := by
    rw [← DivFamZar.mapAlgHom_comp, Over.resAlgHom_comp,
      show ((T.left.basicOpen_le q).trans hW₀ : T.left.basicOpen q ≤ W.1)
        = (hqle.trans (T.left.basicOpen_le r)) from rfl,
      ← Over.resAlgHom_comp T hqle (T.left.basicOpen_le r),
      DivFamZar.mapAlgHom_comp, hzr]
    exact hv.res (ic r hr) ⟨_, W₀.2.basicOpen q⟩ ⟨_, W.2.basicOpen r⟩
      (hqle.trans (hic r hr)) (hic r hr) hqle
  -- the right side restricts the local datum directly
  rw [hL, hv.res i ⟨_, W₀.2.basicOpen q⟩ W₀ ((T.left.basicOpen_le q).trans hi) hi
    (T.left.basicOpen_le q)]
  exact hv.glue (ic r hr) i ⟨_, W₀.2.basicOpen q⟩ (hqle.trans (hic r hr))
    ((T.left.basicOpen_le q).trans hi)

/-! ## Assembling the glued section -/

variable (hcov : ∀ p : T.left, ∃ i, p ∈ O i) (hv : LocalData O v)

/-- The glued value at an affine open of `T.left`. -/
noncomputable def glueValue (W : T.left.affineOpens) : DivFamZar C Γ(T.left, W.1) π n :=
  (exists_isGlueValue hcov hv W).choose

lemma glueValue_spec (W : T.left.affineOpens) :
    IsGlueValue O v W (glueValue hcov hv W) :=
  (exists_isGlueValue hcov hv W).choose_spec

lemma glueValue_eq_of {W : T.left.affineOpens} {z : DivFamZar C Γ(T.left, W.1) π n}
    (hz : IsGlueValue O v W z) : glueValue hcov hv W = z :=
  glueValue_unique hcov (glueValue_spec hcov hv W) hz

/-- **The glued section**: compatible local data on an open cover assembles to a
section of `divFamZar C π n T`. -/
noncomputable def glueSection : divFamZar C π n T :=
  ⟨fun W => glueValue hcov hv W, by
    intro U V h
    beta_reduce
    refine (glueValue_eq_of hcov hv ?_).symm
    intro W₀ hW₀ i hi
    rw [← DivFamZar.mapAlgHom_comp, Over.resAlgHom_comp]
    exact glueValue_spec hcov hv V W₀ (hW₀.trans h) i hi⟩

/-- The glued section restricts to the local datum on each cover member. -/
theorem glueSection_eq (i : ι) (W : T.left.affineOpens) (hW : W.1 ≤ O i) :
    (glueSection hcov hv).1 W = v i W hW := by
  have h := glueValue_spec hcov hv W W le_rfl i hW
  rwa [Over.resAlgHom_rfl, DivFamZar.mapAlgHom_id] at h

include hcov hv in
/-- **The gluing half of the Zariski sheaf property of the locally certified vehicle**
(`informal/spec-dd-2.md` §6, Addendum 2 — the `picEt.existsUnique_glue_of_le_cover`
mirror): a family of local sections on an open cover of `T.left`, compatible on the
affine overlaps (`LocalData`), glues to a unique section of `divFamZar C π n T`
restricting to each. -/
theorem existsUnique_glue_of_le_cover :
    ∃! s : divFamZar C π n T, ∀ (i : ι) (W : T.left.affineOpens) (hW : W.1 ≤ O i),
      s.1 W = v i W hW := by
  refine ⟨glueSection hcov hv, fun i W hW => glueSection_eq hcov hv i W hW,
    fun s hs => ?_⟩
  refine ext_of_le_cover O hcov (fun U i hU => ?_)
  rw [hs i U hU, glueSection_eq hcov hv i U hU]

end divFamZar

end AlgebraicGeometry
