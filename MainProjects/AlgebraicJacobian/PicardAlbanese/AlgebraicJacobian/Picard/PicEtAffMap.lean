/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.PicEtAff

/-!
# Functoriality of the étale plus construction in the test algebra

The étale-plus Picard group `PicEtAff C A` is functorial in the affine test: a base
extension `A → A'` restricts a plus class by base-changing its representing cover
(`Algebra.EtaleCover.baseChange`) and transporting the descent datum along the canonical
inclusion of the carrier into its base change.  Following the mathlib idiom for maps along
base extensions, the extension is carried as instances `[Algebra A A'] [IsScalarTower k A A']`
rather than as an explicit `k`-algebra map.

* `AlgebraicGeometry.descentBaseChange C A' E`: transport of descent classes along the base
  change of the cover — well-posed because the two coprojections of the base-changed double
  cover restrict to `A`-algebra maps out of the original carrier, so the keystone
  `relPicAlgMap_congr` applies.
* `AlgebraicGeometry.PicEtAff.map C A'`: the induced restriction homomorphism
  `PicEtAff C A →* PicEtAff C A'`.
* `AlgebraicGeometry.PicEtAff.map_unit`: naturality of the unit of the plus construction.
* `AlgebraicGeometry.PicEtAff.map_id`, `AlgebraicGeometry.PicEtAff.map_map`: the functor
  laws — both are instances of `relPicAlgMap_congr`, which erases the difference between
  any two transports out of the same descent class.

Together with the unit (`PicEtAff.unit`), this is the presheaf structure of the one-step
étale plus of the relative Picard functor on affine tests; the comparison theorems
(separatedness, rigidification under a section) consume this interface.
-/

set_option autoImplicit false

universe u

open CategoryTheory

open scoped TensorProduct

namespace AlgebraicGeometry

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable {A : Type u} [CommRing A] [Algebra k A]
variable (A' : Type u) [CommRing A'] [Algebra k A'] [Algebra A A'] [IsScalarTower k A A']

noncomputable section

/-! ## Transport of descent classes along base change of the cover -/

/-- The descent condition survives base change of the cover: the two coprojections of the
base-changed double cover restrict along the canonical inclusion to `A`-algebra maps out
of the original carrier, so `relPicAlgMap_congr` identifies the two pullbacks. -/
lemma baseChangeInclude_mem_descentClasses (E : Algebra.EtaleCover A)
    {x : relPic C (overSpec k E.Carrier)} (hx : x ∈ descentClasses C E) :
    relPicAlgMap C ((E.baseChangeInclude A').restrictScalars k) x
      ∈ descentClasses C (E.baseChange A') := by
  rw [mem_descentClasses_iff, ← relPicAlgMap_comp, ← relPicAlgMap_comp]
  have h₁ : (doubleInl (E.baseChange A')).comp ((E.baseChangeInclude A').restrictScalars k)
      = (((Algebra.TensorProduct.includeLeft (S := A')).restrictScalars A).comp
          (E.baseChangeInclude A')).restrictScalars k :=
    AlgHom.ext fun _ => rfl
  have h₂ : (doubleInr (E.baseChange A')).comp ((E.baseChangeInclude A').restrictScalars k)
      = (((Algebra.TensorProduct.includeRight).restrictScalars A).comp
          (E.baseChangeInclude A')).restrictScalars k :=
    AlgHom.ext fun _ => rfl
  rw [h₁, h₂]
  exact relPicAlgMap_congr C _ _ hx

/-- Transport of descent classes along the base change of the cover. -/
def descentBaseChange (E : Algebra.EtaleCover A) :
    descentClasses C E →* descentClasses C (E.baseChange A') :=
  ((relPicAlgMap C ((E.baseChangeInclude A').restrictScalars k)).comp
    (descentClasses C E).subtype).codRestrict _
    fun x => baseChangeInclude_mem_descentClasses C A' E x.2

@[simp]
lemma descentBaseChange_coe (E : Algebra.EtaleCover A) (x : descentClasses C E) :
    (descentBaseChange C A' E x : relPic C (overSpec k (E.baseChange A').Carrier))
      = relPicAlgMap C ((E.baseChangeInclude A').restrictScalars k)
          (x : relPic C (overSpec k E.Carrier)) :=
  rfl

/-- Base-change transport commutes with refinement transport — the naturality square that
makes the transport descend to the plus quotient. -/
lemma descentMap_baseChangeMap {E F : Algebra.EtaleCover A} (h : E.Carrier →ₐ[A] F.Carrier)
    (x : descentClasses C E) :
    descentMap C (Algebra.EtaleCover.baseChangeMap A' h) (descentBaseChange C A' E x)
      = descentBaseChange C A' F (descentMap C h x) := by
  have hcomp : ((Algebra.EtaleCover.baseChangeMap A' h).restrictScalars k).comp
        ((E.baseChangeInclude A').restrictScalars k)
      = ((F.baseChangeInclude A').restrictScalars k).comp (h.restrictScalars k) := by
    have := Algebra.EtaleCover.baseChangeMap_comp_baseChangeInclude A' h
    calc ((Algebra.EtaleCover.baseChangeMap A' h).restrictScalars k).comp
          ((E.baseChangeInclude A').restrictScalars k)
        = ((((Algebra.EtaleCover.baseChangeMap A' h).restrictScalars A).comp
            (E.baseChangeInclude A')).restrictScalars k) := AlgHom.ext fun _ => rfl
      _ = (((F.baseChangeInclude A').comp h).restrictScalars k) := by rw [this]
      _ = ((F.baseChangeInclude A').restrictScalars k).comp (h.restrictScalars k) :=
          AlgHom.ext fun _ => rfl
  ext
  rw [descentMap_coe, descentBaseChange_coe, descentBaseChange_coe, descentMap_coe,
    ← relPicAlgMap_comp, ← relPicAlgMap_comp, hcomp]

namespace PicEtAff

/-! ## The restriction homomorphism -/

private def mapSig (p : Σ E : Algebra.EtaleCover A, descentClasses C E) :
    Σ E' : Algebra.EtaleCover A', descentClasses C E' :=
  ⟨p.1.baseChange A', descentBaseChange C A' p.1 p.2⟩

/- Stated with the sigma pairs fully destructured, so that no goal ever mentions a
sigma-literal projection. -/
private lemma mapSig_rel {E F' : Algebra.EtaleCover A} {x : descentClasses C E}
    {y : descentClasses C F'} (F : Algebra.EtaleCover A) (f : E.Carrier →ₐ[A] F.Carrier)
    (g : F'.Carrier →ₐ[A] F.Carrier) (hfg : descentMap C f x = descentMap C g y) :
    ∃ (G : Algebra.EtaleCover A')
      (f' : (E.baseChange A').Carrier →ₐ[A'] G.Carrier)
      (g' : (F'.baseChange A').Carrier →ₐ[A'] G.Carrier),
      descentMap C f' (descentBaseChange C A' E x)
        = descentMap C g' (descentBaseChange C A' F' y) :=
  ⟨F.baseChange A', Algebra.EtaleCover.baseChangeMap A' f,
    Algebra.EtaleCover.baseChangeMap A' g, by
      rw [descentMap_baseChangeMap, descentMap_baseChangeMap, hfg]⟩

private lemma mapSig_compat {p q : Σ E : Algebra.EtaleCover A, descentClasses C E}
    (h : p ≈ q) : mapSig C A' p ≈ mapSig C A' q := by
  obtain ⟨F, f, g, hfg⟩ := h
  exact mapSig_rel C A' F f g hfg

private def mapFun : PicEtAff C A → PicEtAff C A' :=
  Quotient.map (mapSig C A') fun _ _ h => mapSig_compat C A' h

private lemma mapFun_mk (E : Algebra.EtaleCover A) (x : descentClasses C E) :
    mapFun C A' (mk C E x) = mk C (E.baseChange A') (descentBaseChange C A' E x) :=
  rfl

private lemma mapFun_mul (a b : PicEtAff C A) :
    mapFun C A' (a * b) = mapFun C A' a * mapFun C A' b := by
  induction a using ind with | _ E x =>
  induction b using ind with | _ F y =>
  have h₁ : mapFun C A' (mk C E x)
      = mk C ((E.prod F).baseChange A')
          (descentBaseChange C A' (E.prod F) (descentMap C (E.prodInl F) x)) := by
    rw [← mk_descentMap C (E.prodInl F) x, mapFun_mk]
  have h₂ : mapFun C A' (mk C F y)
      = mk C ((E.prod F).baseChange A')
          (descentBaseChange C A' (E.prod F) (descentMap C (E.prodInr F) y)) := by
    rw [← mk_descentMap C (E.prodInr F) y, mapFun_mk]
  rw [mk_mul_mk, mapFun_mk, map_mul, ← mk_mul_mk_same, h₁, h₂]

/-- Restriction of étale-plus Picard classes along a base extension `A → A'` of affine
tests: base-change the representing cover and transport the descent datum along the
canonical inclusion of the carrier into its base change. -/
def map : PicEtAff C A →* PicEtAff C A' :=
  MonoidHom.mk' (mapFun C A') (mapFun_mul C A')

@[simp]
lemma map_mk (E : Algebra.EtaleCover A) (x : descentClasses C E) :
    map C A' (mk C E x) = mk C (E.baseChange A') (descentBaseChange C A' E x) :=
  rfl

/-! ## Naturality of the unit and the functor laws -/

/-- The unit of the plus construction is natural in the test algebra. -/
theorem map_unit (x : relPic C (overSpec k A)) :
    map C A' (unit C A x)
      = unit C A' (relPicAlgMap C (IsScalarTower.toAlgHom k A A') x) := by
  have hj : (((Algebra.EtaleCover.self A).baseChangeInclude A').restrictScalars k).comp
        ((Algebra.ofId A (Algebra.EtaleCover.self A).Carrier).restrictScalars k)
      = ((((Algebra.EtaleCover.self A).baseChange A').fromSelf).restrictScalars k).comp
          (((Algebra.ofId A' (Algebra.EtaleCover.self A').Carrier).restrictScalars k).comp
            (IsScalarTower.toAlgHom k A A')) := by
    ext a
    simp only [AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply,
      Algebra.ofId_apply, IsScalarTower.coe_toAlgHom', AlgHom.commutes]
    exact IsScalarTower.algebraMap_apply A A' _ a
  have hval : relPicAlgMap C
        (((Algebra.EtaleCover.self A).baseChangeInclude A').restrictScalars k)
        (relPicAlgMap C
          ((Algebra.ofId A (Algebra.EtaleCover.self A).Carrier).restrictScalars k) x)
      = relPicAlgMap C
          ((((Algebra.EtaleCover.self A).baseChange A').fromSelf).restrictScalars k)
          (relPicAlgMap C
            ((Algebra.ofId A' (Algebra.EtaleCover.self A').Carrier).restrictScalars k)
            (relPicAlgMap C (IsScalarTower.toAlgHom k A A') x)) := by
    rw [← relPicAlgMap_comp, ← relPicAlgMap_comp, ← relPicAlgMap_comp, hj,
      AlgHom.comp_assoc]
  calc map C A' (unit C A x)
      = mk C ((Algebra.EtaleCover.self A).baseChange A')
          (descentMap C ((Algebra.EtaleCover.self A).baseChange A').fromSelf
            ⟨_, tautological_mem_descentClasses C (Algebra.EtaleCover.self A')
              (relPicAlgMap C (IsScalarTower.toAlgHom k A A') x)⟩) :=
        congrArg (mk C ((Algebra.EtaleCover.self A).baseChange A')) (Subtype.ext hval)
    _ = mk C (Algebra.EtaleCover.self A')
          ⟨_, tautological_mem_descentClasses C (Algebra.EtaleCover.self A')
            (relPicAlgMap C (IsScalarTower.toAlgHom k A A') x)⟩ :=
        mk_descentMap C ((Algebra.EtaleCover.self A).baseChange A').fromSelf _
    _ = unit C A' (relPicAlgMap C (IsScalarTower.toAlgHom k A A') x) := rfl

/-- Restriction along the trivial base extension is the identity. -/
theorem map_id (a : PicEtAff C A) : map C A a = a := by
  induction a using ind with | _ E x =>
  have h : descentBaseChange C A E x = descentMap C (E.baseChangeInclude A) x := by
    ext
    rw [descentBaseChange_coe, descentMap_coe]
  rw [map_mk, h, mk_descentMap]

section map_map

variable (A'' : Type u) [CommRing A''] [Algebra k A''] [Algebra A A''] [Algebra A' A'']
  [IsScalarTower k A A''] [IsScalarTower k A' A''] [IsScalarTower A A' A'']

/-- Restriction along a composite base extension is the composite of the restrictions —
an instance of `relPicAlgMap_congr`: the one-step and two-step transports are two
`A`-algebra maps out of the same descent class. -/
theorem map_map (a : PicEtAff C A) : map C A'' (map C A' a) = map C A'' a := by
  induction a using ind with | _ E x =>
  rw [map_mk, map_mk, map_mk]
  set BC := E.baseChange A'' with hBC
  set BC₂ := (E.baseChange A').baseChange A'' with hBC₂
  refine (mk_eq_mk_iff C).mpr ⟨BC.prod BC₂, BC.prodInr BC₂, BC.prodInl BC₂, ?_⟩
  have hcongr := relPicAlgMap_congr C
    (((BC.prodInr BC₂).restrictScalars A).comp
      ((((E.baseChange A').baseChangeInclude A'').restrictScalars A).comp
        (E.baseChangeInclude A')))
    (((BC.prodInl BC₂).restrictScalars A).comp (E.baseChangeInclude A''))
    x.2
  ext
  rw [descentMap_coe, descentMap_coe, descentBaseChange_coe, descentBaseChange_coe,
    descentBaseChange_coe, ← relPicAlgMap_comp, ← relPicAlgMap_comp, ← relPicAlgMap_comp]
  calc relPicAlgMap C
        (((BC.prodInr BC₂).restrictScalars k).comp
          ((((E.baseChange A').baseChangeInclude A'').restrictScalars k).comp
            ((E.baseChangeInclude A').restrictScalars k)))
        (x : relPic C (overSpec k E.Carrier))
      = relPicAlgMap C
          ((((BC.prodInr BC₂).restrictScalars A).comp
            ((((E.baseChange A').baseChangeInclude A'').restrictScalars A).comp
              (E.baseChangeInclude A'))).restrictScalars k) x := by
        rw [show (((BC.prodInr BC₂).restrictScalars A).comp
            ((((E.baseChange A').baseChangeInclude A'').restrictScalars A).comp
              (E.baseChangeInclude A'))).restrictScalars k
          = ((BC.prodInr BC₂).restrictScalars k).comp
              ((((E.baseChange A').baseChangeInclude A'').restrictScalars k).comp
                ((E.baseChangeInclude A').restrictScalars k)) from AlgHom.ext fun _ => rfl]
    _ = relPicAlgMap C
          ((((BC.prodInl BC₂).restrictScalars A).comp
            (E.baseChangeInclude A'')).restrictScalars k) x := hcongr
    _ = relPicAlgMap C
          (((BC.prodInl BC₂).restrictScalars k).comp
            ((E.baseChangeInclude A'').restrictScalars k)) x := by
        rw [show (((BC.prodInl BC₂).restrictScalars A).comp
            (E.baseChangeInclude A'')).restrictScalars k
          = ((BC.prodInl BC₂).restrictScalars k).comp
              ((E.baseChangeInclude A'').restrictScalars k) from AlgHom.ext fun _ => rfl]

end map_map

/-! ## Restriction along an explicit algebra map

The presheaf-on-algebras face of the functoriality: for consumers indexing tests by
`k`-algebra maps (limits over affine opens, the relative-Picard comparison), the base
extension is recovered from the map by `RingHom.toAlgebra`.  The instance-parameterized
`PicEtAff.map` remains the preferred form whenever a scalar tower is already in scope. -/

section mapAlg

variable {A' : Type u} [CommRing A'] [Algebra k A']

/-- Restriction of étale-plus Picard classes along an explicit `k`-algebra map of affine
tests. -/
def mapAlg (φ : A →ₐ[k] A') : PicEtAff C A →* PicEtAff C A' :=
  letI : Algebra A A' := φ.toRingHom.toAlgebra
  haveI : IsScalarTower k A A' :=
    .of_algebraMap_eq fun a => (φ.commutes a).symm
  map C A'

/-- `mapAlg` along the identity is the identity. -/
theorem mapAlg_id (a : PicEtAff C A) : mapAlg C (AlgHom.id k A) a = a :=
  map_id C a

/-- The unit of the plus construction is natural in the test algebra, explicit-map form. -/
theorem mapAlg_unit (φ : A →ₐ[k] A') (x : relPic C (overSpec k A)) :
    mapAlg C φ (unit C A x) = unit C A' (relPicAlgMap C φ x) := by
  letI : Algebra A A' := φ.toRingHom.toAlgebra
  haveI : IsScalarTower k A A' :=
    .of_algebraMap_eq fun a => (φ.commutes a).symm
  have hφ : IsScalarTower.toAlgHom k A A' = φ := AlgHom.ext fun _ => rfl
  rw [mapAlg, map_unit, hφ]

variable {A'' : Type u} [CommRing A''] [Algebra k A'']

/-- `mapAlg` along a composite is the composite of the restrictions. -/
theorem mapAlg_comp (φ : A →ₐ[k] A') (ψ : A' →ₐ[k] A'') (a : PicEtAff C A) :
    mapAlg C (ψ.comp φ) a = mapAlg C ψ (mapAlg C φ a) :=
  letI : Algebra A A' := φ.toRingHom.toAlgebra
  haveI : IsScalarTower k A A' :=
    .of_algebraMap_eq fun x => (φ.commutes x).symm
  letI : Algebra A' A'' := ψ.toRingHom.toAlgebra
  haveI : IsScalarTower k A' A'' :=
    .of_algebraMap_eq fun x => (ψ.commutes x).symm
  letI : Algebra A A'' := (ψ.comp φ).toRingHom.toAlgebra
  haveI : IsScalarTower k A A'' :=
    .of_algebraMap_eq fun x => ((ψ.comp φ).commutes x).symm
  haveI : IsScalarTower A A' A'' := .of_algebraMap_eq fun _ => rfl
  (map_map C A' A'' a).symm

end mapAlg

end PicEtAff

end

end AlgebraicGeometry
