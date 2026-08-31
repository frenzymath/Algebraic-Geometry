/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.PicEtAffMap

/-!
# The parameterized transport core of the étale plus construction

The Wave-7 plumbing shared by the curve-direction functoriality (`PicEtAff.curveMap`,
`Picard/PicEtAffCurveMap.lean`) and the base-field shuffle (`PicEtAff.baseFieldShuffle`,
`Picard/PicEtAffBaseFieldShuffle.lean`): transporting étale-plus Picard classes along a
family of scheme morphisms between the product carriers of two curve bundles — possibly
over *different* base fields — indexed by the literally shared étale covers of the affine
test.

* `AlgebraicGeometry.RelPicTransportFamily kT D E`: the input datum.  For curve bundles
  `D` over `kD` and `E` over `kE`, a family of scheme morphisms
  `hom B : (D ⊗ overSpec kD B).left ⟶ (E ⊗ overSpec kE B).left`, compatible with the
  second projections (`hom_snd`) and natural against pairs of algebra maps with equal
  underlying functions (`hom_naturality`).  The family is indexed by all test algebras
  `B` carrying algebra structures over `kD`, `kE` and a common overfield `kT` in scalar
  towers `kD → kT → B` and `kE → kT → B`; `kT` mediates between the two base fields
  without relating them (`kT = kD = kE` for the curve-morphism family; `kT = L` for the
  base-field shuffle, where `{kD, kE} = {k, L}`).
* `AlgebraicGeometry.RelPicTransportFamily.relPicHom`: the induced transport of relative
  Picard groups, with `relPicHom_mk` and the bilateral naturality square
  `relPicAlgMap_relPicHom` against restriction along same-function algebra-map pairs.
* `AlgebraicGeometry.RelPicTransportFamily.descentHom`: descent classes map to descent
  classes over the shared cover index, commuting with refinement transport
  (`descentHom_descentMap`).
* `AlgebraicGeometry.RelPicTransportFamily.picEtAffHom`: the induced homomorphism
  `PicEtAff E A →* PicEtAff D A` of étale-plus groups, with the `mk`-computation rule
  (`picEtAffHom_mk`), naturality of the unit (`picEtAffHom_unit`), the bilateral
  restriction squares (`map_picEtAffHom`, `mapAlg_picEtAffHom`), and the two-sided
  collapse `picEtAffHom_picEtAffHom` (families with pointwise-inverse scheme morphisms
  induce mutually inverse transports — the `≃*` engine of the base-field shuffle).

Everything is stated through the landed `relPicMk`/`relPic.ind`/`relPicAlgMap` and
`PicEtAff.mk`/`ind`/`mk_eq_mk_iff`/`descentMap` interfaces; nothing unfolds the plus
setoid or the relative Picard quotient beyond them.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
open AlgebraicGeometry.Scheme (CechPic)
open scoped TensorProduct

namespace AlgebraicGeometry

variable {kD kE : Type u} [Field kD] [Field kE]

/-- A transport family between the relative Picard theories of a curve bundle `D` over
`kD` and a curve bundle `E` over `kE`, on affine tests: for every test algebra `B` in
scalar towers over both base fields through a common overfield `kT`, a scheme morphism
between the product carriers, compatible with the second projections and natural in `B`.
Descending along `Scheme.CechPic.map`, such a family induces a transport
`PicEtAff E A →* PicEtAff D A` of étale-plus Picard groups over the literally shared
étale-cover index (`picEtAffHom`). -/
structure RelPicTransportFamily (kT : Type u) [Field kT] [Algebra kD kT] [Algebra kE kT]
    (D : Over (Spec (.of kD))) (E : Over (Spec (.of kE))) where
  /-- The underlying family of scheme morphisms between the product carriers. -/
  hom : ∀ (B : Type u) [CommRing B] [Algebra kD B] [Algebra kE B] [Algebra kT B]
    [IsScalarTower kD kT B] [IsScalarTower kE kT B],
    (D ⊗ overSpec kD B).left ⟶ (E ⊗ overSpec kE B).left
  /-- The family commutes with the second projections (both carriers project to the
  shared scheme `Spec B`). -/
  hom_snd : ∀ (B : Type u) [CommRing B] [Algebra kD B] [Algebra kE B] [Algebra kT B]
    [IsScalarTower kD kT B] [IsScalarTower kE kT B],
    hom B ≫ (snd E (overSpec kE B)).left = (snd D (overSpec kD B)).left
  /-- The family is natural against restriction along any pair of algebra maps over the
  two base fields with equal underlying functions. -/
  hom_naturality : ∀ (B B' : Type u) [CommRing B] [Algebra kD B] [Algebra kE B]
    [Algebra kT B] [IsScalarTower kD kT B] [IsScalarTower kE kT B]
    [CommRing B'] [Algebra kD B'] [Algebra kE B'] [Algebra kT B']
    [IsScalarTower kD kT B'] [IsScalarTower kE kT B']
    (fD : B →ₐ[kD] B') (fE : B →ₐ[kE] B'), (∀ b, fD b = fE b) →
    hom B' ≫ (E ◁ Over.overSpecMap fE).left
      = (D ◁ Over.overSpecMap fD).left ≫ hom B

namespace RelPicTransportFamily

variable {kT : Type u} [Field kT] [Algebra kD kT] [Algebra kE kT]
variable {D : Over (Spec (.of kD))} {E : Over (Spec (.of kE))}
variable (T : RelPicTransportFamily kT D E)

noncomputable section

/-! ## The relative Picard transport -/

section RelPicHom

variable (B : Type u) [CommRing B] [Algebra kD B] [Algebra kE B] [Algebra kT B]
  [IsScalarTower kD kT B] [IsScalarTower kE kT B]

/-- Pullback of Čech classes along the family sends classes pulled back from the shared
test `Spec B` to classes pulled back from `Spec B`: well-definedness of the transport on
the cosets. -/
lemma picFromBase_le_comap_hom :
    picFromBase E (overSpec kE B)
      ≤ (picFromBase D (overSpec kD B)).comap (CechPic.map (T.hom B)) := by
  rintro _ ⟨N, rfl⟩
  refine ⟨N, ?_⟩
  rw [← MonoidHom.comp_apply, ← Scheme.CechPic.map_comp, T.hom_snd]
  rfl

/-- The relative Picard transport induced by the family at a test algebra: pull back
Čech classes along `hom B` and descend to the quotients. -/
def relPicHom : relPic E (overSpec kE B) →* relPic D (overSpec kD B) :=
  QuotientGroup.map (picFromBase E (overSpec kE B)) (picFromBase D (overSpec kD B))
    (CechPic.map (T.hom B)) (T.picFromBase_le_comap_hom B)

@[simp]
lemma relPicHom_mk (L : (E ⊗ overSpec kE B).left.CechPic) :
    T.relPicHom B (relPicMk E (overSpec kE B) L)
      = relPicMk D (overSpec kD B) (CechPic.map (T.hom B) L) :=
  QuotientGroup.map_mk' _ _ _ _ L

end RelPicHom

section RelPicSquare

variable {B B' : Type u} [CommRing B] [Algebra kD B] [Algebra kE B] [Algebra kT B]
  [IsScalarTower kD kT B] [IsScalarTower kE kT B]
  [CommRing B'] [Algebra kD B'] [Algebra kE B'] [Algebra kT B']
  [IsScalarTower kD kT B'] [IsScalarTower kE kT B']

/-- **The bilateral naturality square**: the family transport commutes with restriction
along any pair of algebra maps over the two base fields with equal underlying
functions.  Every compatibility of the plus-level transport reduces to this square. -/
theorem relPicAlgMap_relPicHom (fD : B →ₐ[kD] B') (fE : B →ₐ[kE] B')
    (hf : ∀ b, fD b = fE b) (x : relPic E (overSpec kE B)) :
    relPicAlgMap D fD (T.relPicHom B x) = T.relPicHom B' (relPicAlgMap E fE x) := by
  induction x using relPic.ind with
  | mk L =>
    rw [relPicHom_mk, relPicAlgMap, relPicMap_mk, relPicAlgMap, relPicMap_mk,
      relPicHom_mk]
    refine congrArg (relPicMk D (overSpec kD B')) ?_
    rw [← MonoidHom.comp_apply, ← MonoidHom.comp_apply, ← Scheme.CechPic.map_comp,
      ← Scheme.CechPic.map_comp, T.hom_naturality B B' fD fE hf]

end RelPicSquare

/-- Families with pointwise-inverse scheme morphisms induce mutually inverse relative
Picard transports: the round trip along `T` then `S` is the identity when
`S.hom B ≫ T.hom B = 𝟙`. -/
theorem relPicHom_relPicHom (S : RelPicTransportFamily kT E D)
    (B : Type u) [CommRing B] [Algebra kD B] [Algebra kE B] [Algebra kT B]
    [IsScalarTower kD kT B] [IsScalarTower kE kT B]
    (h : S.hom B ≫ T.hom B = 𝟙 ((E ⊗ overSpec kE B).left))
    (x : relPic E (overSpec kE B)) :
    S.relPicHom B (T.relPicHom B x) = x := by
  induction x using relPic.ind with
  | mk L =>
    rw [relPicHom_mk, relPicHom_mk]
    refine congrArg (relPicMk E (overSpec kE B)) ?_
    rw [← MonoidHom.comp_apply, ← Scheme.CechPic.map_comp, h, Scheme.CechPic.map_id]
    rfl

/-! ## The descent-class transport -/

section Descent

variable {A : Type u} [CommRing A] [Algebra kD A] [Algebra kE A] [Algebra kT A]
  [IsScalarTower kD kT A] [IsScalarTower kE kT A]

/-- The descent condition is preserved by the family transport: the two double-cover
pullbacks of the transported class agree, by the bilateral square at the two coprojections
(which are algebra maps over both base fields with the same underlying function). -/
theorem relPicHom_mem_descentClasses {U : Algebra.EtaleCover A}
    {x : relPic E (overSpec kE U.Carrier)} (hx : x ∈ descentClasses E U) :
    T.relPicHom U.Carrier x ∈ descentClasses D U := by
  rw [mem_descentClasses_iff] at hx ⊢
  rw [T.relPicAlgMap_relPicHom (doubleInl U) (doubleInl U) (fun _ => rfl) x,
    T.relPicAlgMap_relPicHom (doubleInr U) (doubleInr U) (fun _ => rfl) x, hx]

/-- The descent-class transport induced by the family, over the literally shared étale
cover index. -/
def descentHom (U : Algebra.EtaleCover A) :
    descentClasses E U →* descentClasses D U :=
  ((T.relPicHom U.Carrier).comp (descentClasses E U).subtype).codRestrict _
    fun x => T.relPicHom_mem_descentClasses x.2

@[simp]
lemma descentHom_coe (U : Algebra.EtaleCover A) (x : descentClasses E U) :
    (T.descentHom U x : relPic D (overSpec kD U.Carrier))
      = T.relPicHom U.Carrier (x : relPic E (overSpec kE U.Carrier)) :=
  rfl

/-- The descent-class transport commutes with refinement transport — what makes the
plus-level transport well defined on `mk`-equal representatives. -/
theorem descentHom_descentMap {U V : Algebra.EtaleCover A} (h : U.Carrier →ₐ[A] V.Carrier)
    (x : descentClasses E U) :
    T.descentHom V (descentMap E h x) = descentMap D h (T.descentHom U x) := by
  ext
  rw [descentHom_coe, descentMap_coe, descentMap_coe, descentHom_coe,
    T.relPicAlgMap_relPicHom (h.restrictScalars kD) (h.restrictScalars kE)
      (fun _ => rfl)]

/-! ## The étale-plus transport -/

variable (A) in
private def mapSig (p : Σ U : Algebra.EtaleCover A, descentClasses E U) :
    Σ U : Algebra.EtaleCover A, descentClasses D U :=
  ⟨p.1, T.descentHom p.1 p.2⟩

/- Stated with the sigma pairs destructured, so that no goal mentions a sigma-literal
projection. -/
private lemma mapSig_rel {U V : Algebra.EtaleCover A} {x : descentClasses E U}
    {y : descentClasses E V} (F : Algebra.EtaleCover A) (f : U.Carrier →ₐ[A] F.Carrier)
    (g : V.Carrier →ₐ[A] F.Carrier) (hfg : descentMap E f x = descentMap E g y) :
    descentMap D f (T.descentHom U x) = descentMap D g (T.descentHom V y) := by
  rw [← T.descentHom_descentMap f x, ← T.descentHom_descentMap g y, hfg]

private lemma mapSig_compat {p q : Σ U : Algebra.EtaleCover A, descentClasses E U}
    (h : p ≈ q) : T.mapSig A p ≈ T.mapSig A q := by
  obtain ⟨F, f, g, hfg⟩ := h
  exact ⟨F, f, g, T.mapSig_rel F f g hfg⟩

variable (A) in
private def mapFun : PicEtAff E A → PicEtAff D A :=
  Quotient.map (T.mapSig A) fun _ _ h => T.mapSig_compat h

private lemma mapFun_mk (U : Algebra.EtaleCover A) (x : descentClasses E U) :
    T.mapFun A (PicEtAff.mk E U x) = PicEtAff.mk D U (T.descentHom U x) :=
  rfl

private lemma mapFun_mul (a b : PicEtAff E A) :
    T.mapFun A (a * b) = T.mapFun A a * T.mapFun A b := by
  induction a using PicEtAff.ind with | _ U x =>
  induction b using PicEtAff.ind with | _ V y =>
  rw [PicEtAff.mk_mul_mk, mapFun_mk, mapFun_mk, mapFun_mk, PicEtAff.mk_mul_mk, map_mul,
    T.descentHom_descentMap, T.descentHom_descentMap]

variable (A) in
/-- The étale-plus transport induced by the family: a homomorphism of étale-plus Picard
groups over the literally shared cover index, transporting each descent-class
representative by `descentHom`. -/
def picEtAffHom : PicEtAff E A →* PicEtAff D A :=
  MonoidHom.mk' (T.mapFun A) fun a b => T.mapFun_mul a b

@[simp]
lemma picEtAffHom_mk (U : Algebra.EtaleCover A) (x : descentClasses E U) :
    T.picEtAffHom A (PicEtAff.mk E U x) = PicEtAff.mk D U (T.descentHom U x) :=
  rfl

/-- The étale-plus transport is compatible with the unit of the plus construction: on
classes pulled back to the trivial cover, it is the relative Picard transport. -/
theorem picEtAffHom_unit (x : relPic E (overSpec kE A)) :
    T.picEtAffHom A (PicEtAff.unit E A x) = PicEtAff.unit D A (T.relPicHom A x) := by
  refine congrArg (PicEtAff.mk D (Algebra.EtaleCover.self A)) (Subtype.ext ?_)
  rw [descentHom_coe]
  exact (T.relPicAlgMap_relPicHom
    ((Algebra.ofId A (Algebra.EtaleCover.self A).Carrier).restrictScalars kD)
    ((Algebra.ofId A (Algebra.EtaleCover.self A).Carrier).restrictScalars kE)
    (fun _ => rfl) x).symm

/-- Families with pointwise-inverse scheme morphisms induce mutually inverse étale-plus
transports: the round trip along `T` then `S` is the identity when
`S.hom B ≫ T.hom B = 𝟙` for every test algebra.  Two-sided instantiation upgrades the
transport to a `MulEquiv` — the engine of the base-field shuffle. -/
theorem picEtAffHom_picEtAffHom (S : RelPicTransportFamily kT E D)
    (h : ∀ (B : Type u) [CommRing B] [Algebra kD B] [Algebra kE B] [Algebra kT B]
      [IsScalarTower kD kT B] [IsScalarTower kE kT B],
      S.hom B ≫ T.hom B = 𝟙 ((E ⊗ overSpec kE B).left))
    (a : PicEtAff E A) :
    S.picEtAffHom A (T.picEtAffHom A a) = a := by
  induction a using PicEtAff.ind with | _ U x =>
  rw [picEtAffHom_mk, picEtAffHom_mk]
  refine congrArg (PicEtAff.mk E U) (Subtype.ext ?_)
  rw [descentHom_coe, descentHom_coe, T.relPicHom_relPicHom S U.Carrier (h U.Carrier)]

end Descent

/-! ## The bilateral restriction squares -/

section Bilateral

variable {A : Type u} [CommRing A] [Algebra kD A] [Algebra kE A] [Algebra kT A]
  [IsScalarTower kD kT A] [IsScalarTower kE kT A]
  {A' : Type u} [CommRing A'] [Algebra kD A'] [Algebra kE A'] [Algebra kT A']
  [IsScalarTower kD kT A'] [IsScalarTower kE kT A']

/-- The étale-plus transport commutes with restriction along a base extension of affine
tests (instance form): the two transports of a representative land on the literally same
base-changed cover, where they agree by the bilateral square at the canonical
inclusion. -/
theorem map_picEtAffHom [Algebra A A'] [IsScalarTower kD A A'] [IsScalarTower kE A A']
    (a : PicEtAff E A) :
    T.picEtAffHom A' (PicEtAff.map E A' a) = PicEtAff.map D A' (T.picEtAffHom A a) := by
  induction a using PicEtAff.ind with | _ U x =>
  rw [PicEtAff.map_mk, picEtAffHom_mk, picEtAffHom_mk, PicEtAff.map_mk]
  refine congrArg (PicEtAff.mk D (U.baseChange A')) (Subtype.ext ?_)
  rw [descentHom_coe, descentBaseChange_coe, descentBaseChange_coe, descentHom_coe,
    T.relPicAlgMap_relPicHom ((U.baseChangeInclude A').restrictScalars kD)
      ((U.baseChangeInclude A').restrictScalars kE) (fun _ => rfl)]

/-- The étale-plus transport commutes with restriction along an explicit algebra map of
affine tests, stated for a `kT`-algebra map restricted to the two base fields — the
`mapAlg` bilateral square. -/
theorem mapAlg_picEtAffHom (φ : A →ₐ[kT] A') (a : PicEtAff E A) :
    T.picEtAffHom A' (PicEtAff.mapAlg E (φ.restrictScalars kE) a)
      = PicEtAff.mapAlg D (φ.restrictScalars kD) (T.picEtAffHom A a) := by
  letI : Algebra A A' := φ.toRingHom.toAlgebra
  haveI : IsScalarTower kD A A' :=
    .of_algebraMap_eq fun r => ((φ.restrictScalars kD).commutes r).symm
  haveI : IsScalarTower kE A A' :=
    .of_algebraMap_eq fun r => ((φ.restrictScalars kE).commutes r).symm
  change T.picEtAffHom A' (PicEtAff.map E A' a) = PicEtAff.map D A' (T.picEtAffHom A a)
  exact T.map_picEtAffHom a

end Bilateral

end

end RelPicTransportFamily

end AlgebraicGeometry
