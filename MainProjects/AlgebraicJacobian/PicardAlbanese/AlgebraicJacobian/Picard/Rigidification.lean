/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.PicEtAff
import AlgebraicJacobian.Picard.UniversalSections

/-!
# Rigidification of relative Picard classes along a section (Kleiman `df:rgd`/`lm:idn`)

For a curve `C` over `k` and a test object `T`, a point `σ : T ⟶ C` of the curve (a
morphism in `Over (Spec k)`) determines a **section of the projection**
`Over.sectionOfPoint σ : T ⟶ C ⊗ T`, `sectionOfPoint σ ≫ snd C T = 𝟙 T` — Kleiman's
`g_T` (*The Picard Scheme*, §2.5).  A Čech Picard class `L` on the product is
**rigidified** along `σ` (`Over.IsRigidified`) when its pullback along the section is
trivial — the cocycle form of Kleiman's `g`-rigidification `u : 𝒪_T ≅ g_T^* L`
(`df:rgd`): on the cocycle model an isomorphism class carries no datum, so "a choice of
trivialization exists" is exactly "`σ^* L = 1`".

This file proves the cocycle recast of Kleiman's Lemma `lm:idn` (rigidified pairs are
carried isomorphically onto the relative Picard group) and its consequences for descent
classes, the (C2) comparison bricks G0–G2 of
`informal/zeta-c2-rigidification-recon.md`:

* **G0** — `Over.sectionOfPoint` with its projection identities
  (`sectionOfPoint_fst`, `sectionOfPoint_snd`), its naturality in the test object
  (`sectionOfPoint_naturality`), and the retraction identity
  `Over.cechPicMap_sectionOfPoint_snd`: `σ`-pullback retracts projection pullback on
  Čech Picard groups.
* **G1 = `lm:idn` surjectivity** — `relPic.exists_isRigidified_rep`: every relative
  Picard class has a rigidified representative, the twist
  `L := M ⋅ (p^* σ^* M)⁻¹` of any representative `M`.
* **`lm:idn` injectivity** — `Over.IsRigidified.eq_of_relPicMk_eq`: two rigidified
  classes representing the same relative Picard class are equal **on the nose**; in
  particular a rigidified representative of the identity is `1`
  (`Over.IsRigidified.eq_one_of_relPicMk_eq_one`).
* **The rigidified transport keystone** — `Over.IsRigidified.cechPicMap_congr`: a
  *rigidified* representative of a descent class (`descentClasses`,
  `AlgebraicJacobian.Picard.PicEtAff`) pulls back **equally on the nose** along any two
  `A`-algebra maps out of the cover carrier — the class-level descent equation
  `p₁^* λ' = p₂^* λ'` of the étale plus construction, upgraded by rigidification from an
  equality of `relPic` classes to an equality of Čech Picard classes.  Specialized to
  the double cover: `Over.IsRigidified.cechPicMap_doubleInl_eq_doubleInr`.  This is the
  entry point of the (C2) surjectivity core (gap G3 of the recon): the honest descent
  datum for the invertible sheaf will be built from this on-the-nose equation.
* **G2 = `lm:aut` ring heart** — `Over.isIso_appTop_sectionOfPoint` /
  `Over.unitsAppLE_sectionOfPoint_bijective`: over an affine test, pullback of global
  (unit) sections along the section of the projection is bijective, because it retracts
  the projection pullback, which is an isomorphism by universal triviality of global
  sections (`Over.universalSections`, Kleiman `ex:gc&r`).  Consequently a global unit
  on the product restricting to `1` along the section is `1` — every automorphism of a
  rigidified pair is trivial.

Design note: the section enters as a **theorem hypothesis** `σ : T ⟶ C` (the frozen
challenge `Curve` carries no point; design §7.3), never as a `HasRationalPoint` class,
and rigidification is a `Prop` on classes, never `Nonempty`-wrapped data.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open AlgebraicGeometry.Scheme (CechPic)

open scoped TensorProduct

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}

namespace Over

/-! ## G0: the section of the projection attached to a curve point -/

section sectionOfPoint

variable {T T' : Over (Spec (.of k))}

/-- The section of the projection `snd C T : C ⊗ T ⟶ T` attached to a `T`-point
`σ : T ⟶ C` of the curve: Kleiman's `g_T` (*The Picard Scheme*, proof of Thm. 2.5(2)).
By the universal property of the cartesian product, `T`-points of `C` and sections of
the projection are the same datum. -/
noncomputable def sectionOfPoint (σ : T ⟶ C) : T ⟶ C ⊗ T :=
  lift σ (𝟙 T)

@[simp]
lemma sectionOfPoint_fst (σ : T ⟶ C) : sectionOfPoint σ ≫ fst C T = σ :=
  lift_fst σ (𝟙 T)

@[simp]
lemma sectionOfPoint_snd (σ : T ⟶ C) : sectionOfPoint σ ≫ snd C T = 𝟙 T :=
  lift_snd σ (𝟙 T)

/-- Naturality of the section in the test object: for `g : T' ⟶ T`, the section of the
`T'`-point `g ≫ σ` composed with the whiskering `C ◁ g` is `g` followed by the section
of `σ`. -/
lemma sectionOfPoint_naturality (g : T' ⟶ T) (σ : T ⟶ C) :
    g ≫ sectionOfPoint σ = sectionOfPoint (g ≫ σ) ≫ (C ◁ g) := by
  refine hom_ext _ _ ?_ ?_
  · rw [Category.assoc, sectionOfPoint_fst, Category.assoc, whiskerLeft_fst,
      sectionOfPoint_fst]
  · rw [Category.assoc, sectionOfPoint_snd, Category.comp_id, Category.assoc,
      whiskerLeft_snd, ← Category.assoc, sectionOfPoint_snd, Category.id_comp]

/-- **The retraction identity** on Čech Picard groups: pullback along the section of the
projection retracts pullback along the projection — `g_T^* ∘ f_T^* = 1` in Kleiman's
notation. -/
lemma cechPicMap_sectionOfPoint_snd (σ : T ⟶ C) (N : T.left.CechPic) :
    CechPic.map (sectionOfPoint σ).left (CechPic.map (snd C T).left N) = N := by
  rw [← MonoidHom.comp_apply, ← Scheme.CechPic.map_comp, ← Over.comp_left,
    sectionOfPoint_snd, Over.id_left, Scheme.CechPic.map_id]
  rfl

end sectionOfPoint

/-! ## Rigidified classes and `lm:idn` -/

section IsRigidified

variable {T T' : Over (Spec (.of k))}

/-- A Čech Picard class on the curve product `C ⊗ T` is **rigidified** along a curve
point `σ : T ⟶ C` when its pullback along the section of the projection is trivial —
the cocycle form of Kleiman's `g`-rigidification (`df:rgd`): on the cocycle model, the
existence of a trivialization `u : 𝒪_T ≅ g_T^* L` is exactly `g_T^* L = 1`. -/
def IsRigidified (σ : T ⟶ C) (L : (C ⊗ T).left.CechPic) : Prop :=
  CechPic.map (sectionOfPoint σ).left L = 1

/-- Unfolding lemma for `IsRigidified`, in rewrite-ready equation form. -/
lemma IsRigidified.map_eq {σ : T ⟶ C} {L : (C ⊗ T).left.CechPic}
    (hL : IsRigidified σ L) : CechPic.map (sectionOfPoint σ).left L = 1 :=
  hL

lemma isRigidified_one (σ : T ⟶ C) : IsRigidified σ (1 : (C ⊗ T).left.CechPic) :=
  map_one (CechPic.map (sectionOfPoint σ).left)

/-- Rigidified classes are stable under restriction of the test object: the pullback of
a `σ`-rigidified class along `C ◁ g` is rigidified along the restricted point
`g ≫ σ`. -/
theorem IsRigidified.cechPicMap (g : T' ⟶ T) {σ : T ⟶ C} {L : (C ⊗ T).left.CechPic}
    (hL : IsRigidified σ L) :
    IsRigidified (g ≫ σ) (CechPic.map (C ◁ g).left L) := by
  change CechPic.map (sectionOfPoint (g ≫ σ)).left (CechPic.map (C ◁ g).left L) = 1
  rw [← MonoidHom.comp_apply, ← Scheme.CechPic.map_comp, ← Over.comp_left,
    ← sectionOfPoint_naturality g σ, Over.comp_left, Scheme.CechPic.map_comp,
    MonoidHom.comp_apply, hL.map_eq, map_one]

/-- **Kleiman `lm:idn`, injectivity, cocycle form**: two rigidified Čech Picard classes
representing the same relative Picard class are equal on the nose.  The ratio is pulled
back from the base, and applying the retraction `Over.cechPicMap_sectionOfPoint_snd`
shows the base class is trivial. -/
theorem IsRigidified.eq_of_relPicMk_eq {σ : T ⟶ C} {L L' : (C ⊗ T).left.CechPic}
    (hL : IsRigidified σ L) (hL' : IsRigidified σ L')
    (h : relPicMk C T L = relPicMk C T L') : L = L' := by
  obtain ⟨N, hN⟩ := (mem_picFromBase_iff (C := C)).mp ((relPicMk_eq_relPicMk_iff C).mp h)
  have hN1 : N = 1 :=
    calc N = CechPic.map (sectionOfPoint σ).left (CechPic.map (snd C T).left N) :=
          (cechPicMap_sectionOfPoint_snd σ N).symm
      _ = CechPic.map (sectionOfPoint σ).left (L / L') := by rw [hN]
      _ = CechPic.map (sectionOfPoint σ).left L
            / CechPic.map (sectionOfPoint σ).left L' := map_div _ L L'
      _ = 1 := by rw [hL.map_eq, hL'.map_eq, div_one]
  have hdiv : L / L' = 1 := by
    rw [← hN, hN1, map_one]
  exact div_eq_one.mp hdiv

/-- A rigidified representative of the identity relative Picard class is `1` on the
nose — `lm:idn` injectivity at the identity. -/
theorem IsRigidified.eq_one_of_relPicMk_eq_one {σ : T ⟶ C} {L : (C ⊗ T).left.CechPic}
    (hL : IsRigidified σ L) (h : relPicMk C T L = 1) : L = 1 :=
  hL.eq_of_relPicMk_eq (isRigidified_one σ) (by rw [h, map_one])

end IsRigidified

end Over

/-! ## G1: existence of a rigidified representative (`lm:idn` surjectivity) -/

section exists_rep

variable {T : Over (Spec (.of k))}

/-- **Kleiman `lm:idn`, surjectivity, cocycle form**: every relative Picard class has a
rigidified representative — the identity-rigidification twist `L := M ⋅ (p^* σ^* M)⁻¹`
of an arbitrary representative `M` (Kleiman: `ℒ := ℳ ⊗ (f_T^* g_T^* ℳ)⁻¹`).  The twist
factor is pulled back from the base, so the relative class is unchanged, and the
`σ`-pullback of the twist is trivial by the retraction identity. -/
theorem relPic.exists_isRigidified_rep (σ : T ⟶ C) (x : relPic C T) :
    ∃ L : (C ⊗ T).left.CechPic, Over.IsRigidified σ L ∧ relPicMk C T L = x := by
  obtain ⟨M, hM⟩ := relPicMk_surjective C T x
  refine ⟨M * (CechPic.map (snd C T).left
    (CechPic.map (Over.sectionOfPoint σ).left M))⁻¹, ?_, ?_⟩
  · change CechPic.map (Over.sectionOfPoint σ).left
      (M * (CechPic.map (snd C T).left
        (CechPic.map (Over.sectionOfPoint σ).left M))⁻¹) = 1
    rw [map_mul, map_inv, Over.cechPicMap_sectionOfPoint_snd, mul_inv_cancel]
  · have hbase : relPicMk C T (CechPic.map (snd C T).left
        (CechPic.map (Over.sectionOfPoint σ).left M)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr
        ⟨CechPic.map (Over.sectionOfPoint σ).left M, rfl⟩
    rw [map_mul, map_inv, hbase, inv_one, mul_one, hM]

end exists_rep

/-! ## The rigidified transport keystone: descent classes on the nose -/

section keystone

variable {A : Type u} [CommRing A] [Algebra k A]

namespace Over

/-- Compatibility of the base-changed sections: restricting the section attached to a
point `σ` over `A` along `Spec` of an `A`-algebra map `j` of covers lands at the section
attached to the canonical point over the target algebra. -/
private lemma overSpecMap_comp_section {E : Algebra.EtaleCover A} {R : Type u}
    [CommRing R] [Algebra k R] [Algebra A R] [IsScalarTower k A R]
    (j : E.Carrier →ₐ[A] R) (σ : overSpec k A ⟶ C) :
    Over.overSpecMap (j.restrictScalars k)
        ≫ (Over.overSpecMap ((Algebra.ofId A E.Carrier).restrictScalars k) ≫ σ)
      = Over.overSpecMap ((Algebra.ofId A R).restrictScalars k) ≫ σ := by
  have key : (j.restrictScalars k).comp ((Algebra.ofId A E.Carrier).restrictScalars k)
      = (Algebra.ofId A R).restrictScalars k := by
    refine AlgHom.ext fun a => ?_
    change j (Algebra.ofId A E.Carrier a) = Algebra.ofId A R a
    rw [Algebra.ofId_apply, Algebra.ofId_apply]
    exact j.commutes a
  rw [← Category.assoc, ← Over.overSpecMap_comp, key]

/-- **The rigidified transport keystone** (the class-level heart of the (C2)
surjectivity core): a rigidified representative of a descent class pulls back equally
**on the nose** along `Spec` of any two `A`-algebra maps out of the cover carrier.

`relPicAlgMap_congr` (the keystone of the plus construction,
`AlgebraicJacobian.Picard.PicEtAff`) provides the equality of *relative Picard* classes;
both pullbacks are rigidified along the section over `R` attached to `σ`
(`IsRigidified.cechPicMap` plus the fact that the `j_i` are `A`-algebra maps), so
`lm:idn` injectivity (`IsRigidified.eq_of_relPicMk_eq`) upgrades the coset equality to
an equality of Čech Picard classes. -/
theorem IsRigidified.cechPicMap_congr {E : Algebra.EtaleCover A} {R : Type u}
    [CommRing R] [Algebra k R] [Algebra A R] [IsScalarTower k A R]
    (j₁ j₂ : E.Carrier →ₐ[A] R) (σ : overSpec k A ⟶ C)
    {L : (C ⊗ overSpec k E.Carrier).left.CechPic}
    (hmem : relPicMk C (overSpec k E.Carrier) L ∈ descentClasses C E)
    (hrig : IsRigidified
      (Over.overSpecMap ((Algebra.ofId A E.Carrier).restrictScalars k) ≫ σ) L) :
    CechPic.map (C ◁ Over.overSpecMap (j₁.restrictScalars k)).left L
      = CechPic.map (C ◁ Over.overSpecMap (j₂.restrictScalars k)).left L := by
  -- the relative-class equality, from the plus-construction keystone
  have hrel : relPicMk C (overSpec k R)
        (CechPic.map (C ◁ Over.overSpecMap (j₁.restrictScalars k)).left L)
      = relPicMk C (overSpec k R)
        (CechPic.map (C ◁ Over.overSpecMap (j₂.restrictScalars k)).left L) :=
    calc relPicMk C (overSpec k R)
          (CechPic.map (C ◁ Over.overSpecMap (j₁.restrictScalars k)).left L)
        = relPicAlgMap C (j₁.restrictScalars k) (relPicMk C _ L) :=
          (relPicMap_mk C (Over.overSpecMap (j₁.restrictScalars k)) L).symm
      _ = relPicAlgMap C (j₂.restrictScalars k) (relPicMk C _ L) :=
          relPicAlgMap_congr C j₁ j₂ hmem
      _ = relPicMk C (overSpec k R)
          (CechPic.map (C ◁ Over.overSpecMap (j₂.restrictScalars k)).left L) :=
          relPicMap_mk C (Over.overSpecMap (j₂.restrictScalars k)) L
  -- both pullbacks are rigidified along the section over `R`
  have hrig₁ := overSpecMap_comp_section j₁ σ ▸
    hrig.cechPicMap (Over.overSpecMap (j₁.restrictScalars k))
  have hrig₂ := overSpecMap_comp_section j₂ σ ▸
    hrig.cechPicMap (Over.overSpecMap (j₂.restrictScalars k))
  exact hrig₁.eq_of_relPicMk_eq hrig₂ hrel

/-- **The descent equation of a rigidified representative holds on the nose**: for a
rigidified representative `L` of a descent class on an étale cover, the two pullbacks of
`L` to the double cover `Spec (B ⊗[A] B)` are *equal Čech Picard classes* — not merely
equal relative classes.  This is Kleiman's rigidified pair `(ℒ', u')` having a
*canonical* comparison on the double cover, the input to the (C2) descent-datum
construction (recon gap G3). -/
theorem IsRigidified.cechPicMap_doubleInl_eq_doubleInr {E : Algebra.EtaleCover A}
    (σ : overSpec k A ⟶ C) {L : (C ⊗ overSpec k E.Carrier).left.CechPic}
    (hmem : relPicMk C (overSpec k E.Carrier) L ∈ descentClasses C E)
    (hrig : IsRigidified
      (Over.overSpecMap ((Algebra.ofId A E.Carrier).restrictScalars k) ≫ σ) L) :
    CechPic.map (C ◁ Over.overSpecMap (doubleInl E)).left L
      = CechPic.map (C ◁ Over.overSpecMap (doubleInr E)).left L := by
  have h₁ : doubleInl E
      = (Algebra.TensorProduct.includeLeft :
          E.Carrier →ₐ[A] E.Carrier ⊗[A] E.Carrier).restrictScalars k :=
    AlgHom.ext fun _ => rfl
  have h₂ : doubleInr E
      = (Algebra.TensorProduct.includeRight :
          E.Carrier →ₐ[A] E.Carrier ⊗[A] E.Carrier).restrictScalars k :=
    AlgHom.ext fun _ => rfl
  rw [h₁, h₂]
  exact IsRigidified.cechPicMap_congr (R := E.Carrier ⊗[A] E.Carrier)
    Algebra.TensorProduct.includeLeft Algebra.TensorProduct.includeRight σ hmem hrig

end Over

end keystone

/-! ## G2: automorphism triviality (`lm:aut`), ring heart -/

section aut

variable [IsProper C.hom] [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]
variable {A : Type u} [CommRing A] [Algebra k A]

namespace Over

/-- **`lm:aut`, ring heart**: over an affine test, pullback of global sections along the
section of the projection is an isomorphism — it retracts the projection pullback, which
is an isomorphism by universal triviality of global sections
(`Over.isIso_appTop_snd_overSpec`, Kleiman `ex:gc&r`). -/
theorem isIso_appTop_sectionOfPoint (σ : overSpec k A ⟶ C) :
    IsIso ((sectionOfPoint σ).left.appTop) := by
  have hcomp : (snd C (overSpec k A)).left.appTop ≫ (sectionOfPoint σ).left.appTop
      = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, ← Over.comp_left, sectionOfPoint_snd, Over.id_left,
      Scheme.Hom.id_appTop]
  haveI : IsIso ((snd C (overSpec k A)).left.appTop) :=
    Over.isIso_appTop_snd_overSpec C A
  haveI : IsIso ((snd C (overSpec k A)).left.appTop
      ≫ (sectionOfPoint σ).left.appTop) := by
    rw [hcomp]
    infer_instance
  exact IsIso.of_isIso_comp_left ((snd C (overSpec k A)).left.appTop)
    ((sectionOfPoint σ).left.appTop)

/-- **`lm:aut`, unit form**: over an affine test, pullback of global *unit* sections
along the section of the projection is bijective.  In particular a global unit of the
curve product restricting to `1` along the section is `1`: every automorphism of a
rigidified pair is trivial (Kleiman, *The Picard Scheme*, Lemma `lm:aut`). -/
theorem unitsAppTop_sectionOfPoint_bijective (σ : overSpec k A ⟶ C) :
    Function.Bijective ((sectionOfPoint σ).left.unitsAppLE ⊤ ⊤
      (le_top.trans (Scheme.Hom.preimage_top (sectionOfPoint σ).left).ge)) := by
  haveI := isIso_appTop_sectionOfPoint σ
  haveI : IsIso ((sectionOfPoint σ).left.appLE ⊤ ⊤
      (le_top.trans (Scheme.Hom.preimage_top (sectionOfPoint σ).left).ge)) := by
    have h : (sectionOfPoint σ).left.appLE ⊤ ⊤
        (le_top.trans (Scheme.Hom.preimage_top (sectionOfPoint σ).left).ge)
        = (sectionOfPoint σ).left.appTop :=
      Scheme.Hom.appLE_eq_app _
    rw [h]
    infer_instance
  have hbij := ConcreteCategory.bijective_of_isIso
    ((sectionOfPoint σ).left.appLE ⊤ ⊤
      (le_top.trans (Scheme.Hom.preimage_top (sectionOfPoint σ).left).ge))
  constructor
  · intro a b hab
    exact Units.ext (hbij.injective (congrArg Units.val hab))
  · intro y
    obtain ⟨a, ha⟩ := hbij.surjective (y : Γ((overSpec k A).left, ⊤))
    obtain ⟨b, hb⟩ := hbij.surjective
      ((y⁻¹ : Γ((overSpec k A).left, ⊤)ˣ) : Γ((overSpec k A).left, ⊤))
    have hab : a * b = 1 := by
      apply hbij.injective
      rw [map_mul, ha, hb, map_one]
      exact y.mul_inv
    have hba : b * a = 1 := by rw [mul_comm]; exact hab
    exact ⟨⟨a, b, hab, hba⟩, Units.ext ha⟩

end Over

end aut

end AlgebraicGeometry
