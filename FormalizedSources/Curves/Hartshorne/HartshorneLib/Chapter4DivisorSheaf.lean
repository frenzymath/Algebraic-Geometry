/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter2ModuleKSheaf
import HartshorneLib.Chapter4PrincipalDivisors

/-!
# The sheaf of bounded rational functions

For a complete smooth integral curve `X` over an algebraically closed field, this
file constructs the sheaf `𝒪(D)` attached to a curve divisor.  Its sections on
an open are rational functions whose local orders are bounded by the divisor.
The empty-open branch is explicitly the zero module, which is needed for the
sheaf condition.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace
open AlgebraicGeometry

namespace Hartshorne

/-! ## The function-field module structure -/

noncomputable def functionFieldOverAlgebraMap (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [IsIntegral X] : k →+* X.functionField :=
  (X.presheaf.germ ⊤ (genericPoint X) trivial).hom.comp (X.overAlgebraMap k ⊤)

@[reducible] noncomputable def functionFieldOverModule (k : Type u) [Field k]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))] [IsIntegral X] :
    Module k X.functionField :=
  (functionFieldOverAlgebraMap k X).toModule

attribute [local instance] functionFieldOverModule Scheme.overModule

lemma functionFieldOverModule_smul_def (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [IsIntegral X]
    (r : k) (g : X.functionField) :
    r • g = functionFieldOverAlgebraMap k X r * g := rfl

/-! ## Local order bounds -/

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {X : Over (Spec (CommRingCat.of k))} [IsIntegral X.left]
  [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom]

omit [IsAlgClosed k] [IsProper X.hom] in
lemma orderAt_algebraMap_stalk_le_one {x : X.left} (hx : x ≠ genericPoint X.left)
    (y : X.left.presheaf.stalk x) :
    orderAt X.hom hx (algebraMap (X.left.presheaf.stalk x) X.left.functionField y) ≤ 1 := by
  letI := smoothCurve_stalk_isDiscreteValuationRing X.hom hx
  letI := smoothCurve_stalk_isDedekindDomain X.hom hx
  exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ y

omit [IsAlgClosed k] [IsProper X.hom] in
lemma orderAt_functionFieldOverAlgebraMap_le_one {x : X.left}
    (hx : x ≠ genericPoint X.left) (r : k) :
    orderAt X.hom hx (functionFieldOverAlgebraMap k X.left r) ≤ 1 := by
  set t : Γ(X.left, ⊤) := X.left.overAlgebraMap k ⊤ r
  have hspec : genericPoint X.left ⤳ x := (genericPoint_spec X.left).specializes trivial
  have hcomp := X.left.presheaf.germ_stalkSpecializes (U := ⊤) (y := x) trivial hspec
  have happ := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hcomp) t
  rw [CommRingCat.hom_comp, RingHom.comp_apply] at happ
  have hrw : functionFieldOverAlgebraMap k X.left r =
      algebraMap (X.left.presheaf.stalk x) X.left.functionField
        ((X.left.presheaf.germ ⊤ x trivial).hom t) := happ.symm
  rw [hrw]
  exact orderAt_algebraMap_stalk_le_one hx _

/-! ## Sections and restrictions -/

noncomputable def divisorBound (D : CurveDivisor k X) {x : X.left}
    (hx : x ≠ genericPoint X.left) : WithZero (Multiplicative ℤ) :=
  letI D' : {x : X.left // x ≠ genericPoint X.left} →₀ ℤ := D
  ((Multiplicative.ofAdd (D' ⟨x, hx⟩) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))

@[simp] lemma divisorBound_zero {x : X.left} (hx : x ≠ genericPoint X.left) :
    divisorBound (0 : CurveDivisor k X) hx = 1 := by
  rw [divisorBound]
  rfl

lemma divisorBound_mono {D D' : CurveDivisor k X} (h : D ≤ D') {x : X.left}
    (hx : x ≠ genericPoint X.left) : divisorBound D hx ≤ divisorBound D' hx := by
  simp only [divisorBound, WithZero.coe_le_coe, Multiplicative.ofAdd_le]
  exact Finsupp.le_def.mp h ⟨x, hx⟩

noncomputable def boundedSections (D : CurveDivisor k X) (U : X.left.Opens) :
    Submodule k X.left.functionField where
  carrier := {g | ∀ (x : X.left) (hx : x ≠ genericPoint X.left), x ∈ U →
    orderAt X.hom hx g ≤ divisorBound D hx}
  zero_mem' := fun _ _ _ => by rw [map_zero]; exact zero_le
  add_mem' := fun {g₁ g₂} h₁ h₂ x hx hxU =>
    le_trans (Valuation.map_add _ g₁ g₂) (max_le (h₁ x hx hxU) (h₂ x hx hxU))
  smul_mem' := fun r g hg x hx hxU => by
    rw [functionFieldOverModule_smul_def k X.left, map_mul]
    calc
      orderAt X.hom hx (functionFieldOverAlgebraMap k X.left r) * orderAt X.hom hx g
          ≤ 1 * orderAt X.hom hx g := by
            gcongr
            exact orderAt_functionFieldOverAlgebraMap_le_one hx r
      _ = orderAt X.hom hx g := one_mul _
      _ ≤ _ := hg x hx hxU

lemma mem_boundedSections {D : CurveDivisor k X} {U : X.left.Opens}
    {g : X.left.functionField} :
    g ∈ boundedSections D U ↔ ∀ (x : X.left) (hx : x ≠ genericPoint X.left), x ∈ U →
      orderAt X.hom hx g ≤ divisorBound D hx := Iff.rfl

lemma boundedSections_le_of_le {D : CurveDivisor k X} {U V : X.left.Opens} (h : V ≤ U) :
    boundedSections D U ≤ boundedSections D V :=
  fun _ hg x hx hxV => hg x hx (h hxV)

lemma boundedSections_mono {D D' : CurveDivisor k X} (h : D ≤ D') (U : X.left.Opens) :
    boundedSections D U ≤ boundedSections D' U :=
  fun _ hg x hx hxU => le_trans (hg x hx hxU) (divisorBound_mono h hx)

noncomputable def divisorSections (D : CurveDivisor k X) (U : X.left.Opens) :
    Submodule k X.left.functionField :=
  ⨆ (_ : (U : Set X.left).Nonempty), boundedSections D U

lemma divisorSections_of_nonempty {D : CurveDivisor k X} {U : X.left.Opens}
    (hU : (U : Set X.left).Nonempty) : divisorSections D U = boundedSections D U :=
  iSup_pos hU

@[simp] lemma divisorSections_of_empty {D : CurveDivisor k X} {U : X.left.Opens}
    (hU : ¬ (U : Set X.left).Nonempty) : divisorSections D U = ⊥ :=
  iSup_neg hU

lemma divisorSections_subsingleton_of_empty {D : CurveDivisor k X} {U : X.left.Opens}
    (hU : ¬ (U : Set X.left).Nonempty) : Subsingleton (divisorSections D U) := by
  rw [divisorSections_of_empty hU]
  infer_instance

lemma mem_divisorSections_of_nonempty {D : CurveDivisor k X} {U : X.left.Opens}
    (hU : (U : Set X.left).Nonempty) {g : X.left.functionField} :
    g ∈ divisorSections D U ↔ ∀ (x : X.left) (hx : x ≠ genericPoint X.left), x ∈ U →
      orderAt X.hom hx g ≤ divisorBound D hx := by
  rw [divisorSections_of_nonempty hU]
  exact mem_boundedSections

lemma divisorSections_antitone {D : CurveDivisor k X} {U V : X.left.Opens} (h : V ≤ U)
    (hV : (V : Set X.left).Nonempty) : divisorSections D U ≤ divisorSections D V := by
  rw [divisorSections_of_nonempty (hV.mono h), divisorSections_of_nonempty hV]
  exact boundedSections_le_of_le h

open Classical in
noncomputable def divisorSectionsRes (D : CurveDivisor k X) {U V : X.left.Opens} (h : V ≤ U) :
    divisorSections D U →ₗ[k] divisorSections D V :=
  if hV : (V : Set X.left).Nonempty then Submodule.inclusion (divisorSections_antitone h hV)
  else 0

lemma divisorSectionsRes_coe {D : CurveDivisor k X} {U V : X.left.Opens} (h : V ≤ U)
    (hV : (V : Set X.left).Nonempty) (s : divisorSections D U) :
    ((divisorSectionsRes D h s : divisorSections D V) : X.left.functionField) =
      (s : X.left.functionField) := by
  classical
  rw [divisorSectionsRes, dif_pos hV, Submodule.coe_inclusion]

lemma divisorSectionsRes_id {D : CurveDivisor k X} {U : X.left.Opens} (h : U ≤ U) :
    divisorSectionsRes D h = LinearMap.id := by
  apply LinearMap.ext
  intro s
  by_cases hU : (U : Set X.left).Nonempty
  · exact Subtype.ext (divisorSectionsRes_coe h hU s)
  · letI := divisorSections_subsingleton_of_empty (D := D) hU
    exact Subsingleton.elim _ _

lemma divisorSectionsRes_comp {D : CurveDivisor k X} {U V W : X.left.Opens} (hWV : W ≤ V)
    (hVU : V ≤ U) :
    divisorSectionsRes D (le_trans hWV hVU) =
      (divisorSectionsRes D hWV).comp (divisorSectionsRes D hVU) := by
  apply LinearMap.ext
  intro s
  by_cases hW : (W : Set X.left).Nonempty
  · have hV : (V : Set X.left).Nonempty := hW.mono hWV
    apply Subtype.ext
    rw [LinearMap.comp_apply, divisorSectionsRes_coe (le_trans hWV hVU) hW,
      divisorSectionsRes_coe hWV hW, divisorSectionsRes_coe hVU hV]
  · letI := divisorSections_subsingleton_of_empty (D := D) hW
    exact Subsingleton.elim _ _

/-! ## The presheaf and sheaf -/

noncomputable def divisorPresheaf (D : CurveDivisor k X) :
    (X.left.Opens)ᵒᵖ ⥤ ModuleCat.{u} k where
  obj U := ModuleCat.of k (divisorSections D U.unop)
  map {U V} i := ModuleCat.ofHom (divisorSectionsRes D (leOfHom i.unop))
  map_id U := by
    apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_ofHom, ModuleCat.hom_id,
      divisorSectionsRes_id (leOfHom (𝟙 U.unop))]
  map_comp {U V W} i j := by
    apply ModuleCat.hom_ext
    have hcomp : divisorSectionsRes D (leOfHom (i ≫ j).unop) =
        (divisorSectionsRes D (leOfHom j.unop)).comp
          (divisorSectionsRes D (leOfHom i.unop)) :=
      divisorSectionsRes_comp (leOfHom j.unop) (leOfHom i.unop)
    simp only [ModuleCat.hom_ofHom, ModuleCat.hom_comp, hcomp]

def divisorVal {D : CurveDivisor k X} {W : X.left.Opens}
    (s : (divisorPresheaf D).obj (op W)) : X.left.functionField :=
  have s' : divisorSections D W := s
  (s' : X.left.functionField)

lemma divisorVal_coe {D : CurveDivisor k X} {W : X.left.Opens}
    (s : divisorSections D W) : divisorVal (D := D) (W := W) s = (s : X.left.functionField) := rfl

lemma divisorVal_mem {D : CurveDivisor k X} {W : X.left.Opens}
    (s : (divisorPresheaf D).obj (op W)) : divisorVal s ∈ divisorSections D W := Subtype.property s

lemma divisorPresheaf_map_val {D : CurveDivisor k X} {U V : (X.left.Opens)ᵒᵖ} (i : U ⟶ V)
    (hV : (V.unop : Set X.left).Nonempty) (s : (divisorPresheaf D).obj U) :
    divisorVal ((divisorPresheaf D).map i s) = divisorVal s :=
  divisorSectionsRes_coe (leOfHom i.unop) hV s

lemma divisorSection_ext {D : CurveDivisor k X} {W : X.left.Opens}
    {a b : (divisorPresheaf D).obj (op W)} (h : divisorVal a = divisorVal b) : a = b :=
  Subtype.ext h

lemma divisorPresheaf_obj_subsingleton {D : CurveDivisor k X} {W : X.left.Opens}
    (hW : ¬ (W : Set X.left).Nonempty) :
    Subsingleton (ToType ((divisorPresheaf D).obj (op W))) :=
  divisorSections_subsingleton_of_empty hW

omit [IsAlgClosed k] [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom] in
lemma opens_inf_nonempty {U V : X.left.Opens} (hU : (U : Set X.left).Nonempty)
    (hV : (V : Set X.left).Nonempty) : (↑(U ⊓ V) : Set X.left).Nonempty := by
  rw [Opens.coe_inf]
  have h := PreirreducibleSpace.isPreirreducible_univ (↑U : Set X.left) (↑V : Set X.left)
    U.isOpen V.isOpen (by simpa using hU) (by simpa using hV)
  simpa using h

lemma isSheaf_divisorPresheaf (D : CurveDivisor k X) :
    Presheaf.IsSheaf (Opens.grothendieckTopology (X.left : TopCat)) (divisorPresheaf D) := by
  have hsh : TopCat.Presheaf.IsSheaf (divisorPresheaf D) := by
    rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
    intro ι U sf hcompat
    have hval : ∀ i j, (U i : Set X.left).Nonempty → (U j : Set X.left).Nonempty →
        divisorVal (sf i) = divisorVal (sf j) := by
      intro i j hi hj
      have hmeet := opens_inf_nonempty hi hj
      have e1 := divisorPresheaf_map_val (Opens.infLELeft (U i) (U j)).op hmeet (sf i)
      have e2 := divisorPresheaf_map_val (Opens.infLERight (U i) (U j)).op hmeet (sf j)
      rw [← e1, ← e2, hcompat i j]
    by_cases hsup : (↑(iSup U) : Set X.left).Nonempty
    · obtain ⟨i₀, hi₀⟩ : ∃ i₀, (U i₀ : Set X.left).Nonempty := by
        rw [Opens.coe_iSup] at hsup
        obtain ⟨x, hx⟩ := hsup
        obtain ⟨i₀, hxi⟩ := Set.mem_iUnion.mp hx
        exact ⟨i₀, ⟨x, hxi⟩⟩
      have hg₀ : divisorVal (sf i₀) ∈ divisorSections D (iSup U) := by
        rw [mem_divisorSections_of_nonempty hsup]
        intro x hx hxmem
        obtain ⟨j, hxj⟩ := Opens.mem_iSup.mp hxmem
        have hjne : (U j : Set X.left).Nonempty := ⟨x, hxj⟩
        rw [hval i₀ j hi₀ hjne]
        exact (mem_divisorSections_of_nonempty hjne).mp (divisorVal_mem (sf j)) x hx hxj
      refine ⟨⟨_, hg₀⟩, ?_, ?_⟩
      · intro i
        by_cases hUi : (U i : Set X.left).Nonempty
        · apply divisorSection_ext
          rw [divisorPresheaf_map_val (Opens.leSupr U i).op hUi]
          exact hval i₀ i hi₀ hUi
        · letI := divisorPresheaf_obj_subsingleton (D := D) hUi
          exact Subsingleton.elim _ _
      · intro y hy
        refine divisorSection_ext ?_
        change divisorVal y = divisorVal (sf i₀)
        rw [← divisorPresheaf_map_val (Opens.leSupr U i₀).op hi₀ y, hy i₀]
    · refine ⟨0, ?_, ?_⟩
      · intro i
        have hUi : ¬ (U i : Set X.left).Nonempty := fun hne => hsup (hne.mono (le_iSup U i))
        letI := divisorPresheaf_obj_subsingleton (D := D) hUi
        exact Subsingleton.elim _ _
      · intro y _
        letI := divisorPresheaf_obj_subsingleton (D := D) hsup
        exact Subsingleton.elim _ _
  exact hsh

noncomputable def divisorSheaf (D : CurveDivisor k X) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology (X.left : TopCat)) (ModuleCat.{u} k) :=
  ⟨divisorPresheaf D, isSheaf_divisorPresheaf D⟩

@[simp] lemma divisorSheaf_obj (D : CurveDivisor k X) (U : X.left.Opens) :
    (divisorSheaf D).obj.obj (op U) = ModuleCat.of k (divisorSections D U) := rfl

lemma divisorSections_mono {D D' : CurveDivisor k X} (h : D ≤ D') (U : X.left.Opens) :
    divisorSections D U ≤ divisorSections D' U :=
  iSup_mono (fun _ => boundedSections_mono h U)

noncomputable def divisorPresheafLE {D D' : CurveDivisor k X} (h : D ≤ D') :
    divisorPresheaf D ⟶ divisorPresheaf D' where
  app U := ModuleCat.ofHom (Submodule.inclusion (divisorSections_mono h U.unop))
  naturality {U V} i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    by_cases hV : (V.unop : Set X.left).Nonempty
    · apply Subtype.ext
      change ((Submodule.inclusion (divisorSections_mono h V.unop))
          (divisorSectionsRes D (leOfHom i.unop) s) : X.left.functionField) =
        (divisorSectionsRes D' (leOfHom i.unop)
          (Submodule.inclusion (divisorSections_mono h U.unop) s) : X.left.functionField)
      rw [Submodule.coe_inclusion, divisorSectionsRes_coe (leOfHom i.unop) hV,
        divisorSectionsRes_coe (leOfHom i.unop) hV, Submodule.coe_inclusion]
    · letI := divisorPresheaf_obj_subsingleton (D := D') (W := V.unop) hV
      exact Subsingleton.elim _ _

noncomputable def divisorSheafLE {D D' : CurveDivisor k X} (h : D ≤ D') :
    divisorSheaf D ⟶ divisorSheaf D' :=
  (fullyFaithfulSheafToPresheaf _ _).preimage (divisorPresheafLE h)

instance divisorSheafLE_mono {D D' : CurveDivisor k X} (h : D ≤ D') :
    Mono (divisorSheafLE h) := by
  haveI happ : ∀ U, Mono ((divisorPresheafLE h).app U) := fun U => by
    rw [ModuleCat.mono_iff_injective]
    exact Submodule.inclusion_injective (divisorSections_mono h U.unop)
  haveI hpre : Mono (divisorPresheafLE h) := NatTrans.mono_of_mono_app _
  have hmap : (sheafToPresheaf _ _).map (divisorSheafLE h) = divisorPresheafLE h :=
    (fullyFaithfulSheafToPresheaf _ _).map_preimage
      (X := divisorSheaf D) (Y := divisorSheaf D') (divisorPresheafLE h)
  apply (sheafToPresheaf _ _).mono_of_mono_map
  rw [hmap]
  exact hpre

end Hartshorne
