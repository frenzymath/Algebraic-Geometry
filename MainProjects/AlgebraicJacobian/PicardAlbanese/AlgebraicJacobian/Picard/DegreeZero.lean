/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.PicEtAff
import AlgebraicJacobian.RiemannRoch.RelPicDegree

/-!
# The degree on the étale plus construction (gap G-D6, worksheet SB-6)

For the challenge curve `C` over `k` and a field extension `K` of `k`, a class of the
étale plus construction `PicEtAff C K` is represented by a descent class on an étale
cover of `Spec K`, and every cover is refined by a single finite separable field
extension `L/K` (cofinality, `Algebra.EtaleCover.exists_finiteSeparableField_algHom`).
On a field representative the relative degree `relPicDeg L` (SB-5) reads an honest
integer, and the **zigzag (WD)** shows this value does not depend on any choice.

* `AlgebraicGeometry.relPicDeg_relPicAlgMap_congr` — leg (i) of the zigzag: a descent
  class read through any two `K`-algebra maps into finite separable field extensions
  has one degree.  The two readings are compared inside a field refinement of the
  product of the two field covers; the transport choice is immaterial by the landed
  keystone `relPicAlgMap_congr`, and the value along each leg is invariant by
  `relPicDeg_relPicAlgMap` (E-iv-alg descended).
* `AlgebraicGeometry.relPicDeg_eq_of_descentMap_eq` — **the zigzag (WD)**: field
  readings of two descent-class representatives identified after transport to a common
  refinement agree.  No Galois theory appears: Galois twisting of the transport is a
  special case of `relPicAlgMap_congr`.
* `AlgebraicGeometry.PicEtAff.degAff K : PicEtAff C K → ℤ` — the degree of an
  étale-locally trivial relative Picard class, by `Quotient.lift` of the reading
  through a *chosen* field refinement, with (WD) as the compatibility proof.
  `Classical.choice` only ever picks representatives; the value is pinned by the
  equality lemma `degAff_mk`.
* `AlgebraicGeometry.PicEtAff.degAff_mk` — **the master equality**: on `mk C E x` the
  degree is the reading of `x` through *any* `K`-algebra map of the cover carrier into
  a finite separable field extension.
* `AlgebraicGeometry.PicEtAff.degAff_mk_ofField` — the anchor on field covers:
  `degAff (mk C (ofField L) y)` is `relPicDeg L` of `y` transported through the carrier
  identification `ofFieldEquiv`.
* `AlgebraicGeometry.PicEtAff.degAff_one`/`degAff_mul`/`degAff_inv` — additivity.
* `AlgebraicGeometry.PicEtAff.degAff_unit` — the unit normalization
  `degAff (unit C K z) = relPicDeg K z`, consumed by G-D8's degree certificates.

The `degAt`/`pic0Functor` endpoints (SB-7) consuming this interface live in
`AlgebraicJacobian.Picard.Pic0Functor`.
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]

noncomputable section

/-! ## The `relPicDeg` calculus -/

/-- The relative degree of a product of relative Picard classes is the sum of the
degrees (`relPicDeg` is a homomorphism from the multiplicative relative Picard group,
stated on the multiplicative product for direct use). -/
theorem relPicDeg_mul (K : Type u) [Field K] [Algebra k K]
    (x y : relPic C (overSpec k K)) :
    relPicDeg K (x * y) = relPicDeg K x + relPicDeg K y :=
  (relPicDeg K).map_add x y

/-- The relative degree of the trivial class is zero. -/
@[simp]
theorem relPicDeg_one (K : Type u) [Field K] [Algebra k K] :
    relPicDeg K (1 : relPic C (overSpec k K)) = 0 :=
  (relPicDeg K).map_zero

/-! ## The zigzag (WD) -/

section Zigzag

variable {K : Type u} [Field K] [Algebra k K]

/-- **Leg (i) of the zigzag (WD)**: a descent class on an étale cover of `Spec K`, read
through any two `K`-algebra maps of the cover carrier into finite separable field
extensions of `K`, has one relative degree.  The two readings are compared inside a
finite separable field refinement of the product of the two field covers: the transport
choice is immaterial by the descent keystone `relPicAlgMap_congr`, and the value along
each comparison leg is invariant by `relPicDeg_relPicAlgMap` (E-iv-alg descended). -/
theorem relPicDeg_relPicAlgMap_congr {E : Algebra.EtaleCover K}
    {x : relPic C (overSpec k E.Carrier)} (hx : x ∈ descentClasses C E)
    {L₁ : Type u} [Field L₁] [Algebra k L₁] [Algebra K L₁] [IsScalarTower k K L₁]
    [Module.Finite K L₁] [Algebra.IsSeparable K L₁]
    {L₂ : Type u} [Field L₂] [Algebra k L₂] [Algebra K L₂] [IsScalarTower k K L₂]
    [Module.Finite K L₂] [Algebra.IsSeparable K L₂]
    (j₁ : E.Carrier →ₐ[K] L₁) (j₂ : E.Carrier →ₐ[K] L₂) :
    relPicDeg L₁ (relPicAlgMap C (j₁.restrictScalars k) x)
      = relPicDeg L₂ (relPicAlgMap C (j₂.restrictScalars k) x) := by
  obtain ⟨M, _, _, _, _, ⟨ℓ⟩⟩ :=
    ((Algebra.EtaleCover.ofField (K := K) L₁).prod
      (Algebra.EtaleCover.ofField (K := K) L₂)).exists_finiteSeparableField_algHom
  letI : Algebra k M := ((algebraMap K M).comp (algebraMap k K)).toAlgebra
  haveI : IsScalarTower k K M := .of_algebraMap_eq fun _ => rfl
  set θ₁ : L₁ →ₐ[K] M :=
    (ℓ.comp ((Algebra.EtaleCover.ofField (K := K) L₁).prodInl
        (Algebra.EtaleCover.ofField (K := K) L₂))).comp
      (Algebra.EtaleCover.ofFieldEquiv (K := K) L₁).symm.toAlgHom with hθ₁
  set θ₂ : L₂ →ₐ[K] M :=
    (ℓ.comp ((Algebra.EtaleCover.ofField (K := K) L₁).prodInr
        (Algebra.EtaleCover.ofField (K := K) L₂))).comp
      (Algebra.EtaleCover.ofFieldEquiv (K := K) L₂).symm.toAlgHom with hθ₂
  calc relPicDeg L₁ (relPicAlgMap C (j₁.restrictScalars k) x)
      = relPicDeg M (relPicAlgMap C (θ₁.restrictScalars k)
          (relPicAlgMap C (j₁.restrictScalars k) x)) :=
        (relPicDeg_relPicAlgMap (θ₁.restrictScalars k) _).symm
    _ = relPicDeg M (relPicAlgMap C ((θ₁.comp j₁).restrictScalars k) x) := by
        rw [show (θ₁.comp j₁).restrictScalars k
            = (θ₁.restrictScalars k).comp (j₁.restrictScalars k) from rfl,
          relPicAlgMap_comp]
    _ = relPicDeg M (relPicAlgMap C ((θ₂.comp j₂).restrictScalars k) x) := by
        rw [relPicAlgMap_congr C (θ₁.comp j₁) (θ₂.comp j₂) hx]
    _ = relPicDeg M (relPicAlgMap C (θ₂.restrictScalars k)
          (relPicAlgMap C (j₂.restrictScalars k) x)) := by
        rw [show (θ₂.comp j₂).restrictScalars k
            = (θ₂.restrictScalars k).comp (j₂.restrictScalars k) from rfl,
          relPicAlgMap_comp]
    _ = relPicDeg L₂ (relPicAlgMap C (j₂.restrictScalars k) x) :=
        relPicDeg_relPicAlgMap (θ₂.restrictScalars k) _

/-- **The zigzag (WD)** — well-definedness of the plus-class degree, both axes in one
lemma: two descent-class representatives identified after transport to a common
refinement (`descentMap C f x₁ = descentMap C g x₂`, the plus-construction setoid) have
equal field readings, through *any* field refinements.  Route: refine the common cover
`G` to a single finite separable field (cofinality), compare each reading with the
reading through the refined leg by `relPicDeg_relPicAlgMap_congr`, and cross over along
the descent equality.  No Galois theory appears. -/
theorem relPicDeg_eq_of_descentMap_eq {E₁ E₂ G : Algebra.EtaleCover K}
    {x₁ : descentClasses C E₁} {x₂ : descentClasses C E₂}
    {f : E₁.Carrier →ₐ[K] G.Carrier} {g : E₂.Carrier →ₐ[K] G.Carrier}
    (hfg : descentMap C f x₁ = descentMap C g x₂)
    {L₁ : Type u} [Field L₁] [Algebra k L₁] [Algebra K L₁] [IsScalarTower k K L₁]
    [Module.Finite K L₁] [Algebra.IsSeparable K L₁]
    {L₂ : Type u} [Field L₂] [Algebra k L₂] [Algebra K L₂] [IsScalarTower k K L₂]
    [Module.Finite K L₂] [Algebra.IsSeparable K L₂]
    (j₁ : E₁.Carrier →ₐ[K] L₁) (j₂ : E₂.Carrier →ₐ[K] L₂) :
    relPicDeg L₁ (relPicAlgMap C (j₁.restrictScalars k)
        (x₁ : relPic C (overSpec k E₁.Carrier)))
      = relPicDeg L₂ (relPicAlgMap C (j₂.restrictScalars k)
          (x₂ : relPic C (overSpec k E₂.Carrier))) := by
  obtain ⟨N, _, _, _, _, ⟨ℓ⟩⟩ := G.exists_finiteSeparableField_algHom
  letI : Algebra k N := ((algebraMap K N).comp (algebraMap k K)).toAlgebra
  haveI : IsScalarTower k K N := .of_algebraMap_eq fun _ => rfl
  have hcoe : relPicAlgMap C (f.restrictScalars k)
        (x₁ : relPic C (overSpec k E₁.Carrier))
      = relPicAlgMap C (g.restrictScalars k)
        (x₂ : relPic C (overSpec k E₂.Carrier)) :=
    congrArg Subtype.val hfg
  calc relPicDeg L₁ (relPicAlgMap C (j₁.restrictScalars k)
          (x₁ : relPic C (overSpec k E₁.Carrier)))
      = relPicDeg N (relPicAlgMap C ((ℓ.comp f).restrictScalars k)
          (x₁ : relPic C (overSpec k E₁.Carrier))) :=
        relPicDeg_relPicAlgMap_congr x₁.2 j₁ (ℓ.comp f)
    _ = relPicDeg N (relPicAlgMap C (ℓ.restrictScalars k)
          (relPicAlgMap C (f.restrictScalars k)
            (x₁ : relPic C (overSpec k E₁.Carrier)))) := by
        rw [show (ℓ.comp f).restrictScalars k
            = (ℓ.restrictScalars k).comp (f.restrictScalars k) from rfl,
          relPicAlgMap_comp]
    _ = relPicDeg N (relPicAlgMap C (ℓ.restrictScalars k)
          (relPicAlgMap C (g.restrictScalars k)
            (x₂ : relPic C (overSpec k E₂.Carrier)))) := by rw [hcoe]
    _ = relPicDeg N (relPicAlgMap C ((ℓ.comp g).restrictScalars k)
          (x₂ : relPic C (overSpec k E₂.Carrier))) := by
        rw [show (ℓ.comp g).restrictScalars k
            = (ℓ.restrictScalars k).comp (g.restrictScalars k) from rfl,
          relPicAlgMap_comp]
    _ = relPicDeg L₂ (relPicAlgMap C (j₂.restrictScalars k)
          (x₂ : relPic C (overSpec k E₂.Carrier))) :=
        (relPicDeg_relPicAlgMap_congr x₂.2 j₂ (ℓ.comp g)).symm

end Zigzag

/-! ## The chosen field refinement

The degree of a plus class is *computed* on the finite separable field refinement chosen
by `Classical.choice` from the cofinality theorem; every consumer immediately trades the
choice away through the master equality `PicEtAff.degAff_mk`, licensed by the zigzag. -/

section RepField

variable {K : Type u} [Field K] [Algebra k K]

/-- The chosen finite separable field refinement of a presented étale cover of `Spec K`
(cofinality, `Algebra.EtaleCover.exists_finiteSeparableField_algHom`). -/
private def degAffField (E : Algebra.EtaleCover K) : Type u :=
  E.exists_finiteSeparableField_algHom.choose

@[reducible]
private def degAffFieldField (E : Algebra.EtaleCover K) : Field (degAffField E) :=
  E.exists_finiteSeparableField_algHom.choose_spec.choose

attribute [local instance] degAffFieldField

@[reducible]
private def degAffFieldAlgebra (E : Algebra.EtaleCover K) : Algebra K (degAffField E) :=
  E.exists_finiteSeparableField_algHom.choose_spec.choose_spec.choose

attribute [local instance] degAffFieldAlgebra

@[reducible]
private def degAffFieldFinite (E : Algebra.EtaleCover K) :
    Module.Finite K (degAffField E) :=
  E.exists_finiteSeparableField_algHom.choose_spec.choose_spec.choose_spec.choose

attribute [local instance] degAffFieldFinite

@[reducible]
private def degAffFieldSeparable (E : Algebra.EtaleCover K) :
    Algebra.IsSeparable K (degAffField E) :=
  E.exists_finiteSeparableField_algHom.choose_spec.choose_spec.choose_spec.choose_spec.choose

attribute [local instance] degAffFieldSeparable

/-- The `k`-algebra structure of the chosen field refinement: the composite of the
tower `k → K → L`.  Registered at low priority: its base-field parameter is free, so at
default priority it would also fire on `Algebra K (degAffField E)` goals (unifying the
base with `K` through `Algebra.id`) and shadow the chosen `degAffFieldAlgebra` — the
instance-diamond watch of the worksheet (risk 3(b)). -/
@[reducible]
private def degAffFieldAlgebraBase (E : Algebra.EtaleCover K) :
    Algebra k (degAffField E) :=
  ((algebraMap K (degAffField E)).comp (algebraMap k K)).toAlgebra

attribute [local instance 100] degAffFieldAlgebraBase

private theorem degAffFieldTower (E : Algebra.EtaleCover K) :
    IsScalarTower k K (degAffField E) :=
  .of_algebraMap_eq fun _ => rfl

attribute [local instance] degAffFieldTower

/-- The chosen refinement map into the chosen field refinement. -/
private def degAffHom (E : Algebra.EtaleCover K) : E.Carrier →ₐ[K] degAffField E :=
  E.exists_finiteSeparableField_algHom.choose_spec.choose_spec.choose_spec.choose_spec
    |>.choose_spec.some

/-- The underlying function of the plus-class degree: the relative degree of the
representative transported to the chosen field refinement of its cover.  Well-defined
on the plus construction by the zigzag (WD); bundled as `PicEtAff.degAff`. -/
private def degAffFun (p : Σ E : Algebra.EtaleCover K, descentClasses C E) : ℤ :=
  relPicDeg (degAffField p.1) (relPicAlgMap C ((degAffHom p.1).restrictScalars k)
    (p.2 : relPic C (overSpec k p.1.Carrier)))

/-! ## The degree of a plus class -/

variable (K) in
/-- **The degree of an étale-locally trivial relative Picard class** (gap G-D6, brick
SB-6): the relative degree of a representative descent class, read on a finite
separable field refinement of its cover through `relPicDeg` (SB-5).  The representative
and the refinement are chosen (`Classical.choice`), but the value is independent of all
choices by the zigzag (WD) `relPicDeg_eq_of_descentMap_eq` — the compatibility proof of
this `Quotient.lift` — and is pinned against *any* field reading by the master equality
`PicEtAff.degAff_mk`. -/
def PicEtAff.degAff : PicEtAff C K → ℤ :=
  Quotient.lift degAffFun fun p q hpq => by
    obtain ⟨G, f, g, hfg⟩ := hpq
    exact relPicDeg_eq_of_descentMap_eq hfg (degAffHom p.1) (degAffHom q.1)

/-- **The master equality for the plus-class degree**: on the class of a descent-class
representative `x` on the cover `E`, the degree is the relative degree of `x`
transported along *any* `K`-algebra map `j` of the cover carrier into *any* finite
separable field extension `L` of `K`.  This is the equality lemma that pins the value
of `degAff`; all normalizations below are instances of it. -/
theorem PicEtAff.degAff_mk (E : Algebra.EtaleCover K) (x : descentClasses C E)
    (L : Type u) [Field L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Module.Finite K L] [Algebra.IsSeparable K L] (j : E.Carrier →ₐ[K] L) :
    PicEtAff.degAff K (PicEtAff.mk C E x)
      = relPicDeg L (relPicAlgMap C (j.restrictScalars k)
          (x : relPic C (overSpec k E.Carrier))) :=
  relPicDeg_relPicAlgMap_congr x.2 (degAffHom E) j

/-- **The anchor of the plus-class degree on field covers**: on a class represented by
a descent class `y` on the field cover `ofField L`, the degree is the relative degree
over `L` of `y` transported through the carrier identification `ofFieldEquiv`. -/
theorem PicEtAff.degAff_mk_ofField (L : Type u) [Field L] [Algebra k L] [Algebra K L]
    [IsScalarTower k K L] [Module.Finite K L] [Algebra.IsSeparable K L]
    (y : descentClasses C (Algebra.EtaleCover.ofField (K := K) L)) :
    PicEtAff.degAff K (PicEtAff.mk C (Algebra.EtaleCover.ofField (K := K) L) y)
      = relPicDeg L (relPicAlgMap C
          ((Algebra.EtaleCover.ofFieldEquiv (K := K) L).toAlgHom.restrictScalars k)
          (y : relPic C (overSpec k (Algebra.EtaleCover.ofField (K := K) L).Carrier))) :=
  PicEtAff.degAff_mk _ y L (Algebra.EtaleCover.ofFieldEquiv (K := K) L).toAlgHom

end RepField

/-! ## Normalizations: unit and additivity -/

section Calculus

variable {K : Type u} [Field K] [Algebra k K]

/-- The degree of the trivial plus class is zero. -/
@[simp]
theorem PicEtAff.degAff_one : PicEtAff.degAff K (1 : PicEtAff C K) = 0 := by
  rw [PicEtAff.one_def,
    PicEtAff.degAff_mk (.self K) 1 K (Algebra.EtaleCover.selfEquiv K).toAlgHom,
    show ((1 : descentClasses C (.self K))
        : relPic C (overSpec k (Algebra.EtaleCover.self K).Carrier)) = 1 from rfl,
    map_one, relPicDeg_one]

/-- **The unit normalization of the plus-class degree** (needed by G-D8's degree
certificates): on a class pulled back from the base along the unit of the plus
construction, the degree is the relative degree over the base field itself — the
trivial cover is refined by the field cover of `K` itself. -/
theorem PicEtAff.degAff_unit (z : relPic C (overSpec k K)) :
    PicEtAff.degAff K (PicEtAff.unit C K z) = relPicDeg K z := by
  have hrep : PicEtAff.unit C K z
      = PicEtAff.mk C (.self K)
          ⟨relPicAlgMap C
              ((Algebra.ofId K (Algebra.EtaleCover.self K).Carrier).restrictScalars k) z,
            PicEtAff.tautological_mem_descentClasses C (.self K) z⟩ := rfl
  rw [hrep,
    PicEtAff.degAff_mk (.self K) _ K (Algebra.EtaleCover.selfEquiv K).toAlgHom,
    ← relPicAlgMap_comp,
    show ((Algebra.EtaleCover.selfEquiv K).toAlgHom.restrictScalars k).comp
        ((Algebra.ofId K (Algebra.EtaleCover.self K).Carrier).restrictScalars k)
      = AlgHom.id k K from AlgHom.ext fun r => by
        simp [Algebra.ofId_apply],
    relPicAlgMap_id]

/-- **Additivity of the plus-class degree**: the degree of a product of plus classes is
the sum of the degrees.  Represent the product on the product cover (`mk_mul_mk`),
refine to a single finite separable field, and read all three degrees there —
`relPicDeg` is a homomorphism. -/
theorem PicEtAff.degAff_mul (a b : PicEtAff C K) :
    PicEtAff.degAff K (a * b) = PicEtAff.degAff K a + PicEtAff.degAff K b := by
  induction a using PicEtAff.ind with | _ E x =>
  induction b using PicEtAff.ind with | _ F y =>
  obtain ⟨L, _, _, _, _, ⟨ℓ⟩⟩ := (E.prod F).exists_finiteSeparableField_algHom
  letI : Algebra k L := ((algebraMap K L).comp (algebraMap k K)).toAlgebra
  haveI : IsScalarTower k K L := .of_algebraMap_eq fun _ => rfl
  rw [PicEtAff.mk_mul_mk, PicEtAff.degAff_mk (E.prod F) _ L ℓ,
    PicEtAff.degAff_mk E x L (ℓ.comp (E.prodInl F)),
    PicEtAff.degAff_mk F y L (ℓ.comp (E.prodInr F)),
    show ((descentMap C (E.prodInl F) x * descentMap C (E.prodInr F) y :
          descentClasses C (E.prod F))
        : relPic C (overSpec k (E.prod F).Carrier))
      = relPicAlgMap C ((E.prodInl F).restrictScalars k)
          (x : relPic C (overSpec k E.Carrier))
        * relPicAlgMap C ((E.prodInr F).restrictScalars k)
          (y : relPic C (overSpec k F.Carrier)) from rfl,
    map_mul, relPicDeg_mul,
    show (ℓ.comp (E.prodInl F)).restrictScalars k
      = (ℓ.restrictScalars k).comp ((E.prodInl F).restrictScalars k) from rfl,
    show (ℓ.comp (E.prodInr F)).restrictScalars k
      = (ℓ.restrictScalars k).comp ((E.prodInr F).restrictScalars k) from rfl,
    relPicAlgMap_comp, relPicAlgMap_comp]

/-- The degree of an inverse plus class is the negation of the degree. -/
theorem PicEtAff.degAff_inv (a : PicEtAff C K) :
    PicEtAff.degAff K a⁻¹ = -PicEtAff.degAff K a := by
  have h := PicEtAff.degAff_mul a⁻¹ a
  rw [inv_mul_cancel, PicEtAff.degAff_one] at h
  omega

end Calculus

end

end AlgebraicGeometry
