/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.JacobianDataBaseChange
import AlgebraicJacobian.Picard.AbelElement

/-!
# Abel–Jacobi compatibility of the datum-level base change (Wave 7, W7-functor A-1)

For a field embedding `k → L`, the curve bundle `C` over `k`, Jacobian data `d` on `C` and
`dL` on `C_L = (baseChange k L).obj C`, and a `k`-rational point `P : 𝟙_ ⟶ C`, this file
transports the Abel–Jacobi map `d.homEquiv.symm (abelElement C P) : C ⟶ d.J` across base
change and compares it, through the datum-level base-change isomorphism
`baseChangeIsoOfData` (B-6b), with the Abel–Jacobi map of the base-changed point.  This is
the datum-level shape of the frozen `AlgebraicGeometry.Jacobian.baseChange_ofCurve`
(`Challenge.lean:278`), consumed by the DAT-J discharge at `d := jacobianData C`,
`dL := jacobianData C_L`.

## Accessor re-pin (R-K1-3, against the COMMITTED B-6b signature `e30e066a1`)

`baseChangeIsoOfData d dL : (baseChange k L).mapGrp.obj (.mk d.J) ≅ .mk dL.J` is an
isomorphism in `Grp (Over (Spec (.of L)))` — the identical return shape as the frozen
`baseChangeIso` — so its underlying-scheme morphism `(baseChange k L).obj d.J ⟶ dL.J` is
`(baseChangeIsoOfData d dL).hom.hom.hom` (iso `.hom` → `Grp`-morphism, then `Mon`-morphism
`.hom`, then underlying `.hom`), the verbatim accessor of the frozen
`baseChange_ofCurve`.  `L` is IMPLICIT in `baseChangeIsoOfData`, inferred from `dL`'s type;
the call is `baseChangeIsoOfData d dL`.

## Main declarations

* `AlgebraicGeometry.baseChangeIsoOfData_hom_hom_hom` — **the accessor bridge**: the
  underlying morphism of the datum-level base-change isomorphism is the `uniqueUpToIso`
  comparison of the transported datum `d.baseChange L` with `dL`,
  `(baseChangeIsoOfData d dL).hom.hom.hom = ((d.baseChange L).uniqueUpToIso dL).hom`.  Via
  the `eqToIso`/`Grp.mkIso` unfolding of B-6b and `grp_eqToHom_hom_hom`.  Reusable by the
  frozen DAT-J discharge (it is exactly the equation that reduces `baseChangeIso` to
  `uniqueUpToIso`).
* `AlgebraicGeometry.baseChange_homEquiv_map_aj_of_core` /
  `AlgebraicGeometry.baseChange_ofCurve_data_of_core` — the datum-level Abel–Jacobi
  base-change compatibility, reduced to a single **Leg-4 core identity** `hCore` (the
  base-field shuffle θ carries the Abel class across the pushed test).  The reduction is
  complete and axiom-clean: it applies `dL.homEquiv` injectivity, the accessor bridge, the
  `uniqueUpToIso` intertwining `homEquiv_uniqueUpToIso_hom`, the B-5 `RepresentableBy.ofIso`
  unfolding of `(d.baseChange L).homEquiv` (definitional), the `Over.mapPullbackAdj σ` counit
  transpose, and `homEquiv` naturality (`homEquiv_comp`).  What remains — `hCore` — is the
  geometric heart isolated by the ratified `informal/w7-k1-worksheet.md` §3 as Leg 4, "the
  whole mathematical cost":
  ```
  (pic0CrossBaseEquiv k L C C_L).symm
      (pic0Map C ((Over.mapPullbackAdj σ).counit.app C) (abelElement C P))
    = abelElement C_L (Functor.LaxMonoidal.ε (baseChange k L) ≫ (baseChange k L).map P)
  ```
  i.e. underlying-`picEt`,
  `picEtCrossBase k L C C_L (picEtMap C εC (abelPicEt C P)) = abelPicEt C_L Q`.  It is a
  base-field-shuffle-on-graph-class identity, to be closed by `abelPicEt_map` +
  `graphLocalEquations_base_change` (recon §3.4); it is not yet landed.

Once `hCore` is discharged, the frozen `baseChange_ofCurve_data` (worksheet §3) follows by
`baseChange_ofCurve_data_of_core hCore`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

/-- The double-`hom` projection of an `eqToHom` in a bundled `Grp` category is the
`eqToHom` of the underlying-object equality — proved by `subst`.  (Used to collapse the
`eqToIso` core of `baseChangeIsoOfData` to the identity on the shared underlying object.) -/
theorem grp_eqToHom_hom_hom {D : Type*} [Category D] [CartesianMonoidalCategory D]
    {A B : Grp D} (h : A = B) :
    (eqToHom h).hom.hom = eqToHom (congrArg (fun z => z.X) h) := by
  subst h; rfl

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
variable {L : Type u} [Field L] [Algebra k L]

/-- **The accessor bridge** (R-K1-3): the underlying-scheme morphism of the datum-level
base-change isomorphism `baseChangeIsoOfData d dL` is the `uniqueUpToIso` comparison of the
transported datum `d.baseChange L` with `dL`.  Unfolds B-6b's `eqToIso ≪≫ Grp.mkIso`
assembly: the `Grp.mkIso` factor projects to `(uniqueUpToIso).hom` and the `eqToIso` core
collapses to the identity (its two `Grp` objects share the underlying scheme
`(baseChange k L).obj d.J`). -/
theorem baseChangeIsoOfData_hom_hom_hom (d : JacobianData C)
    (dL : JacobianData ((baseChange k L).obj C)) :
    (baseChangeIsoOfData d dL).hom.hom.hom = ((d.baseChange L).uniqueUpToIso dL).hom := by
  unfold baseChangeIsoOfData
  simp only [Iso.trans_hom, Grp.comp_hom_hom, eqToIso.hom, Grp.mkIso_hom_hom_hom]
  rw [grp_eqToHom_hom_hom]
  exact Category.id_comp _

/-- **The core reduction** (Abel–Jacobi under base change, transported-datum side): the
universal class of the base-changed Abel–Jacobi map, read through the transported datum
`d.baseChange L`, is the Abel class of the base-changed point — GIVEN the Leg-4 core
identity `hCore` (θ carries the Abel class across the base-field shuffle).  The reduction is
complete: `(d.baseChange L).homEquiv` unfolds (definitionally, B-5's `RepresentableBy.ofIso`)
to `(pic0CrossBaseEquiv …).symm ∘ d.homEquiv ∘ (adjunction transpose)`; the transpose of
`(baseChange k L).map _` is the `Over.mapPullbackAdj σ` counit precomposition (counit
naturality); and `homEquiv` naturality collapses it to `pic0Map C εC (abelElement C P)`. -/
theorem baseChange_homEquiv_map_aj_of_core (d : JacobianData C)
    (P : 𝟙_ (Over (Spec (.of k))) ⟶ C)
    (hCore : (pic0CrossBaseEquiv k L C ((baseChange k L).obj C)).symm
        (pic0Map C
          ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom (algebraMap k L)))).counit.app C)
          (abelElement C P))
      = abelElement ((baseChange k L).obj C)
          (Functor.LaxMonoidal.ε (baseChange k L) ≫ (baseChange k L).map P)) :
    (d.baseChange L).homEquiv
        ((baseChange k L).map (d.homEquiv.symm (abelElement C P)))
      = abelElement _ (Functor.LaxMonoidal.ε (baseChange k L) ≫ (baseChange k L).map P) := by
  have htrans : ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom (algebraMap k L)))).homEquiv
        ((baseChange k L).obj C) d.J).symm
          ((baseChange k L).map (d.homEquiv.symm (abelElement C P)))
      = (Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom (algebraMap k L)))).counit.app C
          ≫ d.homEquiv.symm (abelElement C P) := by
    rw [Adjunction.homEquiv_counit]
    exact (Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom (algebraMap k L)))).counit_naturality _
  have hAll : d.homEquiv
        (((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom (algebraMap k L)))).homEquiv
          ((baseChange k L).obj C) d.J).symm
            ((baseChange k L).map (d.homEquiv.symm (abelElement C P))))
      = pic0Map C
          ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom (algebraMap k L)))).counit.app C)
          (abelElement C P) :=
    (congrArg d.homEquiv htrans).trans
      ((d.homEquiv_comp _ _).trans (congrArg _ (d.homEquiv.apply_symm_apply _)))
  exact (congrArg (pic0CrossBaseEquiv k L C ((baseChange k L).obj C)).symm hAll).trans hCore

/-- **The datum-level Abel–Jacobi base-change compatibility** (worksheet §3, A-1), GIVEN the
Leg-4 core `hCore`: base change of the Abel–Jacobi map `d.homEquiv.symm (abelElement C P)`,
followed by the datum-level base-change isomorphism, equals the Abel–Jacobi map of the
base-changed point.  Reduced through `dL.homEquiv` injectivity, the accessor bridge
`baseChangeIsoOfData_hom_hom_hom`, the `uniqueUpToIso` intertwining, and
`baseChange_homEquiv_map_aj_of_core`.  Instantiating at `d := jacobianData C`,
`dL := jacobianData C_L` (definitional, `Jacobian C := (jacobianData C).J`) discharges the
frozen `Jacobian.baseChange_ofCurve` once `hCore` is proved. -/
theorem baseChange_ofCurve_data_of_core (d : JacobianData C)
    (dL : JacobianData ((baseChange k L).obj C)) (P : 𝟙_ (Over (Spec (.of k))) ⟶ C)
    (hCore : (pic0CrossBaseEquiv k L C ((baseChange k L).obj C)).symm
        (pic0Map C
          ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom (algebraMap k L)))).counit.app C)
          (abelElement C P))
      = abelElement ((baseChange k L).obj C)
          (Functor.LaxMonoidal.ε (baseChange k L) ≫ (baseChange k L).map P)) :
    (baseChange k L).map (d.homEquiv.symm (abelElement C P))
        ≫ (baseChangeIsoOfData d dL).hom.hom.hom
      = dL.homEquiv.symm
          (abelElement _ (Functor.LaxMonoidal.ε (baseChange k L) ≫ (baseChange k L).map P)) := by
  apply dL.homEquiv.injective
  rw [Equiv.apply_symm_apply]
  have e1 : (baseChange k L).map (d.homEquiv.symm (abelElement C P))
        ≫ (baseChangeIsoOfData d dL).hom.hom.hom
      = (baseChange k L).map (d.homEquiv.symm (abelElement C P))
        ≫ ((d.baseChange L).uniqueUpToIso dL).hom := by
    rw [baseChangeIsoOfData_hom_hom_hom]
  refine Eq.trans (congrArg (dL.homEquiv ·) e1) ?_
  refine Eq.trans ((d.baseChange L).homEquiv_uniqueUpToIso_hom dL _) ?_
  exact baseChange_homEquiv_map_aj_of_core d P hCore

end AlgebraicGeometry
