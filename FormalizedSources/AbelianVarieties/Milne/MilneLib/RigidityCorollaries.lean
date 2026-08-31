/-
Copyright (c) 2026 The Milne Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Milne Contributors
-/

import MilneLib.GroupScheme
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Rigidity corollaries

Additive decomposition and pointed-homomorphism consequences of the group-variety rigidity lemma.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open AlgebraicGeometry

namespace MilneLib.GroupVariety

variable {kbar : Type u} [Field kbar] [IsAlgClosed kbar]

/-! Corollaries of the rigidity lemma (Milne, *Abelian Varieties*, I.1). -/

/-- Additive decomposition of a pointed map out of a product. -/
theorem hom_additive_decomp_of_rigidity
    {V W : Over (Spec (.of kbar))}
    [IsProper V.hom]
    [GeometricallyIrreducible (V ⊗ W).hom]
    [LocallyOfFiniteType (V ⊗ W).hom]
    [IsReduced (V ⊗ W).left]
    {A : Over (Spec (.of kbar))}
    [GrpObj A] [IsSeparated A.hom]
    (v₀ : 𝟙_ (Over (Spec (.of kbar))) ⟶ V)
    (w₀ : 𝟙_ (Over (Spec (.of kbar))) ⟶ W)
    (h : V ⊗ W ⟶ A)
    (hh : lift v₀ w₀ ≫ h = η[A]) :
    h = (fst V W ≫ (lift (𝟙 V) (toUnit V ≫ w₀) ≫ h)) *
        (snd V W ≫ (lift (toUnit W ≫ v₀) (𝟙 W) ≫ h)) := by
  set f : V ⟶ A := lift (𝟙 V) (toUnit V ≫ w₀) ≫ h with hf
  set g : W ⟶ A := lift (toUnit W ≫ v₀) (𝟙 W) ≫ h with hg
  have hsVfst : lift (𝟙 V) (toUnit V ≫ w₀) ≫ fst V W = 𝟙 V := by simp
  have hsVsnd : lift (𝟙 V) (toUnit V ≫ w₀) ≫ snd V W = toUnit V ≫ w₀ := by simp
  have hsWfst : lift (toUnit W ≫ v₀) (𝟙 W) ≫ fst V W = toUnit W ≫ v₀ := by simp
  have hsWsnd : lift (toUnit W ≫ v₀) (𝟙 W) ≫ snd V W = 𝟙 W := by simp
  have hwsW : w₀ ≫ lift (toUnit W ≫ v₀) (𝟙 W) = lift v₀ w₀ := by
    rw [comp_lift, Category.comp_id, ← Category.assoc,
      toUnit_unique (w₀ ≫ toUnit W) (𝟙 _), Category.id_comp]
  have hvsV : v₀ ≫ lift (𝟙 V) (toUnit V ≫ w₀) = lift v₀ w₀ := by
    rw [comp_lift, Category.comp_id, ← Category.assoc,
      toUnit_unique (v₀ ≫ toUnit V) (𝟙 _), Category.id_comp]
  have hwg : w₀ ≫ g = η[A] := by rw [hg, ← Category.assoc, hwsW, hh]
  have hvf : v₀ ≫ f = η[A] := by rw [hf, ← Category.assoc, hvsV, hh]
  set φ : V ⊗ W ⟶ A := h / ((fst V W ≫ f) * (snd V W ≫ g)) with hφ
  have hcolV : lift (𝟙 V) (toUnit V ≫ w₀) ≫ φ = toUnit V ≫ η[A] := by
    rw [← Hom.one_def, hφ, GrpObj.comp_div, ← hf, MonObj.comp_mul,
      ← Category.assoc, hsVfst, Category.id_comp,
      ← Category.assoc, hsVsnd, Category.assoc, hwg, ← Hom.one_def, _root_.mul_one, div_self']
  have hcolW : lift (toUnit W ≫ v₀) (𝟙 W) ≫ φ = (1 : W ⟶ A) := by
    rw [hφ, GrpObj.comp_div, ← hg, MonObj.comp_mul,
      ← Category.assoc, hsWfst, Category.assoc, hvf, ← Hom.one_def,
      ← Category.assoc, hsWsnd, Category.id_comp, _root_.one_mul, div_self']
  obtain ⟨g', hg'⟩ := rigidity_lemma φ v₀ w₀ η[A] hcolV
  have hg'1 : g' = 1 := by
    have hsec : lift (toUnit W ≫ v₀) (𝟙 W) ≫ φ = g' := by
      rw [hg', ← Category.assoc, hsWsnd, Category.id_comp]
    rw [← hsec, hcolW]
  have hφ1 : φ = 1 := by rw [hg', hg'1, MonObj.comp_one]
  have hdiv : h / ((fst V W ≫ f) * (snd V W ≫ g)) = 1 := by rw [← hφ]; exact hφ1
  exact div_eq_one.mp hdiv

/- The additive decomposition is valid over an arbitrary field once the two
   factors are geometrically integral.  The quotient construction is formal;
   only the final constancy step uses scalar extension through the preceding
   arbitrary-field rigidity theorem. -/
theorem hom_additive_decomp_of_rigidity_arbitraryField
    {K : Type u} [Field K]
    {V W : Over (Spec (.of K))}
    [IsProper V.hom]
    [GeometricallyIntegral V.hom]
    [GeometricallyIntegral W.hom]
    [LocallyOfFiniteType W.hom]
    {A : Over (Spec (.of K))}
    [GrpObj A] [IsSeparated A.hom]
    (v₀ : 𝟙_ (Over (Spec (.of K))) ⟶ V)
    (w₀ : 𝟙_ (Over (Spec (.of K))) ⟶ W)
    (h : V ⊗ W ⟶ A)
    (hh : lift v₀ w₀ ≫ h = η[A]) :
    h = (fst V W ≫ (lift (𝟙 V) (toUnit V ≫ w₀) ≫ h)) *
        (snd V W ≫ (lift (toUnit W ≫ v₀) (𝟙 W) ≫ h)) := by
  set f : V ⟶ A := lift (𝟙 V) (toUnit V ≫ w₀) ≫ h with hf
  set g : W ⟶ A := lift (toUnit W ≫ v₀) (𝟙 W) ≫ h with hg
  have hsVfst : lift (𝟙 V) (toUnit V ≫ w₀) ≫ fst V W = 𝟙 V := by simp
  have hsVsnd : lift (𝟙 V) (toUnit V ≫ w₀) ≫ snd V W = toUnit V ≫ w₀ := by simp
  have hsWfst : lift (toUnit W ≫ v₀) (𝟙 W) ≫ fst V W = toUnit W ≫ v₀ := by simp
  have hsWsnd : lift (toUnit W ≫ v₀) (𝟙 W) ≫ snd V W = 𝟙 W := by simp
  have hwsW : w₀ ≫ lift (toUnit W ≫ v₀) (𝟙 W) = lift v₀ w₀ := by
    rw [comp_lift, Category.comp_id, ← Category.assoc,
      toUnit_unique (w₀ ≫ toUnit W) (𝟙 _), Category.id_comp]
  have hvsV : v₀ ≫ lift (𝟙 V) (toUnit V ≫ w₀) = lift v₀ w₀ := by
    rw [comp_lift, Category.comp_id, ← Category.assoc,
      toUnit_unique (v₀ ≫ toUnit V) (𝟙 _), Category.id_comp]
  have hwg : w₀ ≫ g = η[A] := by rw [hg, ← Category.assoc, hwsW, hh]
  have hvf : v₀ ≫ f = η[A] := by rw [hf, ← Category.assoc, hvsV, hh]
  set φ : V ⊗ W ⟶ A := h / ((fst V W ≫ f) * (snd V W ≫ g)) with hφ
  have hcolV : lift (𝟙 V) (toUnit V ≫ w₀) ≫ φ = toUnit V ≫ η[A] := by
    rw [← Hom.one_def, hφ, GrpObj.comp_div, ← hf, MonObj.comp_mul,
      ← Category.assoc, hsVfst, Category.id_comp,
      ← Category.assoc, hsVsnd, Category.assoc, hwg, ← Hom.one_def,
      _root_.mul_one, div_self']
  have hcolW : lift (toUnit W ≫ v₀) (𝟙 W) ≫ φ = (1 : W ⟶ A) := by
    rw [hφ, GrpObj.comp_div, ← hg, MonObj.comp_mul,
      ← Category.assoc, hsWfst, Category.assoc, hvf, ← Hom.one_def,
      ← Category.assoc, hsWsnd, Category.id_comp, _root_.one_mul, div_self']
  have hcolW' : lift (toUnit W ≫ v₀) (𝟙 W) ≫ φ = toUnit W ≫ η[A] := by
    rw [hcolW, Hom.one_def]
  have hφconst := rigidity_constant_of_two_axes_arbitraryField
    (X := V) (Y := W) (Z := A) φ v₀ w₀ η[A] hcolV hcolW'
  have hφ1 : φ = 1 := by
    calc
      φ = toUnit (V ⊗ W) ≫ η[A] := hφconst
      _ = 1 := Hom.one_def.symm
  have hdiv : h / ((fst V W ≫ f) * (snd V W ≫ g)) = 1 := by
    rw [← hφ]
    exact hφ1
  exact div_eq_one.mp hdiv

/- Evaluating a proposed additive decomposition on the two distinguished axes
   recovers its factors.  This is the uniqueness calculation behind Milne's
   product-decomposition corollary. -/
omit [IsAlgClosed kbar] in
theorem hom_additive_decomp_axis_unique
    {V W : Over (Spec (.of kbar))}
    {A : Over (Spec (.of kbar))} [GrpObj A]
    (v₀ : 𝟙_ (Over (Spec (.of kbar))) ⟶ V)
    (w₀ : 𝟙_ (Over (Spec (.of kbar))) ⟶ W)
    (h : V ⊗ W ⟶ A) (f : V ⟶ A) (g : W ⟶ A)
    (hf : v₀ ≫ f = η[A]) (hg : w₀ ≫ g = η[A])
    (hdecomp : h = (fst V W ≫ f) * (snd V W ≫ g)) :
    f = lift (𝟙 V) (toUnit V ≫ w₀) ≫ h ∧
      g = lift (toUnit W ≫ v₀) (𝟙 W) ≫ h := by
  constructor
  · rw [hdecomp, MonObj.comp_mul, ← Category.assoc, lift_fst, Category.id_comp,
      ← Category.assoc, lift_snd, Category.assoc, hg, ← Hom.one_def, _root_.mul_one]
  · rw [hdecomp, MonObj.comp_mul, ← Category.assoc, lift_fst, Category.assoc, hf,
      ← Hom.one_def, ← Category.assoc, lift_snd, Category.id_comp, _root_.one_mul]

/- The existence theorem above and the axis calculation package the
   decomposition as an actual unique pair of pointed factors. -/
theorem existsUnique_hom_additive_decomp_of_rigidity
    {V W : Over (Spec (.of kbar))}
    [IsProper V.hom]
    [GeometricallyIrreducible (V ⊗ W).hom]
    [LocallyOfFiniteType (V ⊗ W).hom]
    [IsReduced (V ⊗ W).left]
    {A : Over (Spec (.of kbar))}
    [GrpObj A] [IsSeparated A.hom]
    (v₀ : 𝟙_ (Over (Spec (.of kbar))) ⟶ V)
    (w₀ : 𝟙_ (Over (Spec (.of kbar))) ⟶ W)
    (h : V ⊗ W ⟶ A)
    (hh : lift v₀ w₀ ≫ h = η[A]) :
    ∃! p : (V ⟶ A) × (W ⟶ A),
      v₀ ≫ p.1 = η[A] ∧ w₀ ≫ p.2 = η[A] ∧
        h = (fst V W ≫ p.1) * (snd V W ≫ p.2) := by
  let f : V ⟶ A := lift (𝟙 V) (toUnit V ≫ w₀) ≫ h
  let g : W ⟶ A := lift (toUnit W ≫ v₀) (𝟙 W) ≫ h
  have hwsW : w₀ ≫ lift (toUnit W ≫ v₀) (𝟙 W) = lift v₀ w₀ := by
    rw [comp_lift, Category.comp_id, ← Category.assoc,
      toUnit_unique (w₀ ≫ toUnit W) (𝟙 _), Category.id_comp]
  have hvsV : v₀ ≫ lift (𝟙 V) (toUnit V ≫ w₀) = lift v₀ w₀ := by
    rw [comp_lift, Category.comp_id, ← Category.assoc,
      toUnit_unique (v₀ ≫ toUnit V) (𝟙 _), Category.id_comp]
  have hwg : w₀ ≫ g = η[A] := by
    change w₀ ≫ (lift (toUnit W ≫ v₀) (𝟙 W) ≫ h) = η[A]
    rw [← Category.assoc, hwsW, hh]
  have hvf : v₀ ≫ f = η[A] := by
    change v₀ ≫ (lift (𝟙 V) (toUnit V ≫ w₀) ≫ h) = η[A]
    rw [← Category.assoc, hvsV, hh]
  have hdecomp := hom_additive_decomp_of_rigidity v₀ w₀ h hh
  refine ⟨(f, g), ⟨hvf, hwg, hdecomp⟩, ?_⟩
  rintro ⟨f', g'⟩ ⟨hf', hg', hd'⟩
  have hu := hom_additive_decomp_axis_unique v₀ w₀ h f' g' hf' hg' hd'
  apply Prod.ext
  · simpa only [f] using hu.1
  · simpa only [g] using hu.2

/-- A pointed morphism of group varieties is a monoid homomorphism. -/
theorem isMonHom_of_pointed
    {A B : Over (Spec (.of kbar))}
    [GrpObj A] [IsProper A.hom]
    [GeometricallyIrreducible (A ⊗ A).hom]
    [LocallyOfFiniteType (A ⊗ A).hom]
    [IsReduced (A ⊗ A).left]
    [GrpObj B] [IsSeparated B.hom]
    (α : A ⟶ B) (hα : η[A] ≫ α = η[B]) : IsMonHom α := by
  have h1 : (η[A] : 𝟙_ (Over (Spec (.of kbar))) ⟶ A) = 1 := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have hbase : lift η[A] η[A] ≫ μ[A] = η[A] := by
    rw [← Hom.mul_def, h1, _root_.mul_one]
  have key := hom_additive_decomp_of_rigidity (V := A) (W := A) (A := B)
    η[A] η[A] (μ[A] ≫ α) (by rw [← Category.assoc, hbase, hα])
  rw [show lift (𝟙 A) (toUnit A ≫ η[A]) ≫ μ[A] ≫ α = α by
        rw [← Category.assoc, lift_comp_one_right, Category.id_comp],
      show lift (toUnit A ≫ η[A]) (𝟙 A) ≫ μ[A] ≫ α = α by
        rw [← Category.assoc, lift_comp_one_left, Category.id_comp]] at key
  exact { one_hom := hα, mul_hom := by rw [key, Hom.mul_def, lift_fst_comp_snd_comp] }

/- The product hypotheses in the preceding theorem are automatic for the
   ordinary abelian-variety package once the base field is algebraically
   closed.  They are installed explicitly here because typeclass synthesis
   does not unfold the tensor object into its pullback presentation. -/
theorem isMonHom_of_pointed_of_isAbelianVariety
    {A B : Over (Spec (.of kbar))} [GrpObj A] [GrpObj B]
    (hA : MilneLib.IsAbelianVariety A)
    (hB : MilneLib.IsAbelianVariety B)
    (α : A ⟶ B) (hα : η[A] ≫ α = η[B]) : IsMonHom α := by
  letI : IsProper A.hom := hA.1
  letI : GeometricallyIntegral A.hom := hA.2
  letI : IsProper B.hom := hB.1
  letI : GeometricallyIntegral B.hom := hB.2
  letI : LocallyOfFiniteType A.hom := IsProper.toLocallyOfFiniteType
  haveI : GeometricallyIrreducible (A ⊗ A).hom := by
    rw [Over.tensorObj_hom]
    exact GeometricallyIrreducible.comp (pullback.fst A.hom A.hom) A.hom
  haveI : LocallyOfFiniteType (A ⊗ A).hom := by
    rw [Over.tensorObj_hom]
    exact AlgebraicGeometry.locallyOfFiniteType_comp
      (pullback.fst A.hom A.hom) A.hom
  letI : IsIntegral (A ⊗ A).left :=
    isIntegral_tensorObj_left_of_geometricallyIntegral (X := A) (Y := A)
  haveI : IsReduced (A ⊗ A).left := inferInstance
  exact isMonHom_of_pointed α hα

/- The pointed-homomorphism criterion descends from an algebraic closure. -/
theorem isMonHom_of_pointed_of_isAbelianVariety_arbitraryField
    {K : Type u} [Field K]
    {A B : Over (Spec (.of K))} [GrpObj A] [GrpObj B]
    (hA : MilneLib.IsAbelianVariety A)
    (hB : MilneLib.IsAbelianVariety B)
    (α : A ⟶ B) (hα : η[A] ≫ α = η[B]) : IsMonHom α := by
  letI : IsProper A.hom := hA.1
  letI : GeometricallyIntegral A.hom := hA.2
  letI : IsProper B.hom := hB.1
  letI : GeometricallyIntegral B.hom := hB.2
  let f := Spec.map (CommRingCat.ofHom <| algebraMap K (AlgebraicClosure K))
  let F := Over.pullback f
  let A' := F.obj A
  let B' := F.obj B
  letI : GrpObj A' := Functor.grpObjObj
  letI : GrpObj B' := Functor.grpObjObj
  have hA' : MilneLib.IsAbelianVariety A' := hA.baseChange f
  have hB' : MilneLib.IsAbelianVariety B' := hB.baseChange f
  have hup : IsMonHom (F.map α) := by
    have hpt : η[A'] ≫ F.map α = η[B'] := by
      simp [← Functor.map_comp, hα]
    exact isMonHom_of_pointed_of_isAbelianVariety hA' hB' (F.map α) hpt
  refine { one_hom := hα, mul_hom := ?_ }
  exact F.map_injective <| by
    simpa [← Functor.LaxMonoidal.μ_natural_assoc,
      ← cancel_epi (Functor.LaxMonoidal.μ F A A)] using IsMonHom.mul_hom (F.map α)

/- Proper geometrically integral group schemes are commutative.  This proof
   records Milne's rigidity route explicitly: the inverse is pointed, hence a
   homomorphism, and inversion of a product reverses its factors. -/
theorem isCommMonObj_of_isAbelianVariety_via_rigidity
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A]
    (hA : MilneLib.IsAbelianVariety A) : IsCommMonObj A := by
  letI : IsMonHom (GrpObj.inv (X := A)) := by
    apply isMonHom_of_pointed_of_isAbelianVariety_arbitraryField hA hA
    exact GrpObj.one_inv
  rw [isCommMonObj_iff_isMulCommutative]
  intro X
  constructor
  constructor
  intro f g
  have key : ∀ u v : X ⟶ A, (u * v) ≫ GrpObj.inv (X := A) =
      (u ≫ GrpObj.inv (X := A)) * (v ≫ GrpObj.inv (X := A)) := by
    intro u v
    rw [Hom.mul_def, Hom.mul_def, Category.assoc, IsMonHom.mul_hom]
    simp [lift_map_assoc]
  have h1 := key f g
  rw [← Hom.inv_def, ← Hom.inv_def, ← Hom.inv_def] at h1
  have h2 : ((f * g)⁻¹)⁻¹ = (f⁻¹ * g⁻¹)⁻¹ := by rw [h1]
  simpa using h2

/-- Every morphism between abelian varieties is a homomorphism followed by a
translation, expressed using the canonical point translation on the target. -/
theorem exists_hom_comp_pointTranslation_of_isAbelianVariety
    {A B : Over (Spec (.of kbar))} [GrpObj A] [GrpObj B]
    (hA : MilneLib.IsAbelianVariety A)
    (hB : MilneLib.IsAbelianVariety B)
    (α : A ⟶ B) :
    ∃ (β : A ⟶ B) (b : 𝟙_ (Over (Spec (.of kbar))) ⟶ B),
      IsMonHom β ∧ η[A] ≫ β = η[B] ∧
        α = β ≫ (pointTranslation B η[B] b).hom := by
  let b := η[A] ≫ α
  let β := α ≫ (pointTranslation B b η[B]).hom
  have hβ : η[A] ≫ β = η[B] := by
    change b ≫ (pointTranslation B b η[B]).hom = η[B]
    exact comp_pointTranslation_hom b η[B]
  have hβhom := isMonHom_of_pointed_of_isAbelianVariety hA hB β hβ
  refine ⟨β, b, hβhom, hβ, ?_⟩
  dsimp [β]
  symm
  rw [Category.assoc, ← Iso.trans_hom, pointTranslation_trans]
  simp

/- The decomposition is likewise valid over an arbitrary base field; only the
   scalar-extension step is new, while the translation calculation is formal. -/
theorem exists_hom_comp_pointTranslation_of_isAbelianVariety_arbitraryField
    {K : Type u} [Field K]
    {A B : Over (Spec (.of K))} [GrpObj A] [GrpObj B]
    (hA : MilneLib.IsAbelianVariety A)
    (hB : MilneLib.IsAbelianVariety B)
    (α : A ⟶ B) :
    ∃ (β : A ⟶ B) (b : 𝟙_ (Over (Spec (.of K))) ⟶ B),
      IsMonHom β ∧ η[A] ≫ β = η[B] ∧
        α = β ≫ (pointTranslation B η[B] b).hom := by
  let b := η[A] ≫ α
  let β := α ≫ (pointTranslation B b η[B]).hom
  have hβ : η[A] ≫ β = η[B] := by
    change b ≫ (pointTranslation B b η[B]).hom = η[B]
    exact comp_pointTranslation_hom b η[B]
  have hβhom := isMonHom_of_pointed_of_isAbelianVariety_arbitraryField hA hB β hβ
  refine ⟨β, b, hβhom, hβ, ?_⟩
  dsimp [β]
  symm
  rw [Category.assoc, ← Iso.trans_hom, pointTranslation_trans]
  simp

/- The pointed factor and translating section in a translation decomposition
   are uniquely determined.  This calculation is formal and does not use
   algebraic closedness or the geometric hypotheses on the source. -/
theorem pointTranslation_decomposition_unique
    {K : Type u} [Field K]
    {A B : Over (Spec (.of K))} [GrpObj A] [GrpObj B]
    {alpha beta₁ beta₂ : A ⟶ B}
    {b₁ b₂ : 𝟙_ (Over (Spec (.of K))) ⟶ B}
    (h₁ : η[A] ≫ beta₁ = η[B])
    (h₂ : η[A] ≫ beta₂ = η[B])
    (ha₁ : alpha = beta₁ ≫ (pointTranslation B η[B] b₁).hom)
    (ha₂ : alpha = beta₂ ≫ (pointTranslation B η[B] b₂).hom) :
    b₁ = b₂ ∧ beta₁ = beta₂ := by
  have hb : b₁ = b₂ := by
    have h := congrArg (fun q => η[A] ≫ q) (ha₁.symm.trans ha₂)
    calc
      b₁ = η[A] ≫ beta₁ ≫ (pointTranslation B η[B] b₁).hom := by
        rw [← Category.assoc, h₁, comp_pointTranslation_hom]
      _ = η[A] ≫ beta₂ ≫ (pointTranslation B η[B] b₂).hom := h
      _ = b₂ := by
        rw [← Category.assoc, h₂, comp_pointTranslation_hom]
  have hcomp :
      beta₁ ≫ (pointTranslation B η[B] b₂).hom =
        beta₂ ≫ (pointTranslation B η[B] b₂).hom := by
    simpa [hb] using ha₁.symm.trans ha₂
  have hcancel := congrArg
    (fun q => q ≫ (pointTranslation B η[B] b₂).inv) hcomp
  have hbeta : beta₁ = beta₂ := by
    simpa [Category.assoc] using hcancel
  exact ⟨hb, hbeta⟩

/- Every morphism of abelian varieties has a unique presentation as a pointed
   homomorphism followed by translation by the image of the identity. -/
theorem existsUnique_hom_comp_pointTranslation_of_isAbelianVariety_arbitraryField
    {K : Type u} [Field K]
    {A B : Over (Spec (.of K))} [GrpObj A] [GrpObj B]
    (hA : MilneLib.IsAbelianVariety A)
    (hB : MilneLib.IsAbelianVariety B)
    (alpha : A ⟶ B) :
    ∃! p : (A ⟶ B) × (𝟙_ (Over (Spec (.of K))) ⟶ B),
      IsMonHom p.1 ∧ η[A] ≫ p.1 = η[B] ∧
        alpha = p.1 ≫ (pointTranslation B η[B] p.2).hom := by
  obtain ⟨beta, b, hbeta, hpointed, hdecomp⟩ :=
    exists_hom_comp_pointTranslation_of_isAbelianVariety_arbitraryField hA hB alpha
  refine ⟨(beta, b), ⟨hbeta, hpointed, hdecomp⟩, ?_⟩
  rintro ⟨beta', b'⟩ ⟨_, hpointed', hdecomp'⟩
  have hunique := pointTranslation_decomposition_unique
    hpointed hpointed' hdecomp hdecomp'
  exact Prod.ext hunique.2.symm hunique.1.symm

/- The arbitrary-field existence theorem also admits the same unique-pair
   packaging as the algebraically closed version.  The axis calculation is
   purely categorical, so no extra algebraic-closure hypothesis is needed. -/
theorem existsUnique_hom_additive_decomp_of_rigidity_arbitraryField
    {K : Type u} [Field K]
    {V W : Over (Spec (.of K))}
    [IsProper V.hom]
    [GeometricallyIntegral V.hom]
    [GeometricallyIntegral W.hom]
    [LocallyOfFiniteType W.hom]
    {A : Over (Spec (.of K))}
    [GrpObj A] [IsSeparated A.hom]
    (v₀ : 𝟙_ (Over (Spec (.of K))) ⟶ V)
    (w₀ : 𝟙_ (Over (Spec (.of K))) ⟶ W)
    (h : V ⊗ W ⟶ A)
    (hh : lift v₀ w₀ ≫ h = η[A]) :
    ∃! p : (V ⟶ A) × (W ⟶ A),
      v₀ ≫ p.1 = η[A] ∧ w₀ ≫ p.2 = η[A] ∧
        h = (fst V W ≫ p.1) * (snd V W ≫ p.2) := by
  let f : V ⟶ A := lift (𝟙 V) (toUnit V ≫ w₀) ≫ h
  let g : W ⟶ A := lift (toUnit W ≫ v₀) (𝟙 W) ≫ h
  have hwsW : w₀ ≫ lift (toUnit W ≫ v₀) (𝟙 W) = lift v₀ w₀ := by
    rw [comp_lift, Category.comp_id, ← Category.assoc,
      toUnit_unique (w₀ ≫ toUnit W) (𝟙 _), Category.id_comp]
  have hvsV : v₀ ≫ lift (𝟙 V) (toUnit V ≫ w₀) = lift v₀ w₀ := by
    rw [comp_lift, Category.comp_id, ← Category.assoc,
      toUnit_unique (v₀ ≫ toUnit V) (𝟙 _), Category.id_comp]
  have hwg : w₀ ≫ g = η[A] := by
    change w₀ ≫ (lift (toUnit W ≫ v₀) (𝟙 W) ≫ h) = η[A]
    rw [← Category.assoc, hwsW, hh]
  have hvf : v₀ ≫ f = η[A] := by
    change v₀ ≫ (lift (𝟙 V) (toUnit V ≫ w₀) ≫ h) = η[A]
    rw [← Category.assoc, hvsV, hh]
  have hdecomp := hom_additive_decomp_of_rigidity_arbitraryField
    (V := V) (W := W) (A := A) v₀ w₀ h hh
  refine ⟨(f, g), ⟨hvf, hwg, hdecomp⟩, ?_⟩
  rintro ⟨f', g'⟩ ⟨hf', hg', hd'⟩
  have hu := hom_additive_decomp_axis_unique (kbar := K)
    v₀ w₀ h f' g' hf' hg' hd'
  apply Prod.ext
  · simpa only [f] using hu.1
  · simpa only [g] using hu.2

end MilneLib.GroupVariety
