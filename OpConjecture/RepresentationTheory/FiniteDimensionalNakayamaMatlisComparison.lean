import OpConjecture.RepresentationTheory.FiniteProjectiveNakayamaEquiv

/-!
# Nakayama--Matlis comparison for finite-dimensional algebras

Let `R` be a finite-dimensional algebra over a field `K`.  For every finite
projective `P` and finite module `Y`, this file packages the canonical
equivalence

`Hom_R(Y, D Hom_R(P,R)) ≃ Hom_K(Hom_R(P,Y), K)`.

It proves naturality both in `Y` and in `P`.  Applying projective naturality
to the differential of an arbitrary two-step projective presentation gives
the scalar `TwoStepNakayamaMatlisComparison` used by the abstract
stable-Hom--Ext construction.

Only general finite-projective and finite-dimensional duality is used; no
quiver algebra or module classification enters the proof.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ModuleCat.Algebra

namespace OpConjecture.AuslanderTranspose.TwoStepProjectivePresentation

open OpConjecture.RingelStable

universe u

namespace FiniteProjectiveNakayama

variable (K R : Type u) [Field K] [Ring R] [Algebra K R]
  [FiniteDimensional K R]
  [IsNoetherianRing R] [IsNoetherianRing Rᵐᵒᵖ]

/-- Categorical morphisms in `FGModuleCat` identified with their underlying
module-linear maps, including the restricted `K`-linear structure. -/
def fgHomCarrierLinearEquiv
    (Y Z : FGModuleCat.{u} R) :
    (Y ⟶ Z) ≃ₗ[K] (Y →ₗ[R] Z) :=
  InducedCategory.homLinearEquiv.trans ModuleCat.homLinearEquiv

variable (P : FGProjectives (R := R))

/-- The tensor-Hom comparison constructed from rank-one maps, before
rebundling categorical morphisms. -/
def nakayamaHomLinearEquiv
    (Y : FGModuleCat.{u} R) :
    Module.Dual K (P.obj →ₗ[R] Y) ≃ₗ[K]
      (Y →ₗ[R] projectiveNakayama (K := K) (R := R) P) :=
  LinearEquiv.ofBijective
    (nakayamaHomLinearMap (K := K) (R := R) P Y)
    (nakayamaHomLinearMap_bijective (K := K) (R := R) P Y)

/-- The projective-variable Nakayama--Hom comparison over a field. -/
def fieldNakayamaHomEquiv
    (Y : FGModuleCat.{u} R) :
    (Y ⟶ projectiveNakayama (K := K) (R := R) P) ≃ₗ[K]
      ((P.obj ⟶ Y) →ₗ[K] K) :=
  (fgHomCarrierLinearEquiv K R Y
      (projectiveNakayama (K := K) (R := R) P)).trans <|
    (nakayamaHomLinearEquiv (K := K) (R := R) P Y).symm |>.trans <|
      (LinearEquiv.congrLeft K K
        (fgHomCarrierLinearEquiv K R P.obj Y)).symm

omit [IsNoetherianRing R] in
@[simp]
theorem fieldNakayamaHomEquiv_rankOne
    (Y : FGModuleCat.{u} R)
    (a : Y ⟶ projectiveNakayama (K := K) (R := R) P)
    (q : (projectiveHomDual (R := R) P).obj) (y : Y) :
    fieldNakayamaHomEquiv (K := K) (R := R) P Y a
        (FGModuleCat.ofHom (rankOne (R := R) P Y q y)) =
      projectiveNakayamaEvaluation (K := K) (R := R) P (a.hom.hom y) q := by
  let e := nakayamaHomLinearEquiv (K := K) (R := R) P Y
  let ell := e.symm a.hom.hom
  have h := e.apply_symm_apply a.hom.hom
  have hy := LinearMap.congr_fun h y
  have hq := LinearMap.congr_fun hy q
  exact hq

include K in
omit [FiniteDimensional K R] [IsNoetherianRing R] in
/-- The finite rank-one expansion, rebundled as an equality of categorical
morphisms. -/
theorem categoricalRankOneFrameSum
    (Y : FGModuleCat.{u} R) (f : P.obj ⟶ Y) :
    ∑ i, FGModuleCat.ofHom
        (rankOne (R := R) P Y
          ((projectiveHomDualFrame (R := R) P).q i)
          (f.hom.hom (finiteProjectiveFrameElement (R := R) P i))) = f := by
  apply (fgHomCarrierLinearEquiv K R P.obj Y).injective
  rw [map_sum]
  change
    ∑ i, rankOne (R := R) P Y
        ((projectiveHomDualFrame (R := R) P).q i)
        (f.hom.hom (finiteProjectiveFrameElement (R := R) P i)) = f.hom.hom
  exact rankOneFrameSum (R := R) P Y f.hom.hom

omit [IsNoetherianRing R] in
/-- Every value of the comparison is the corresponding finite dual-frame
sum. -/
theorem fieldNakayamaHomEquiv_apply_eq_sum
    (Y : FGModuleCat.{u} R)
    (a : Y ⟶ projectiveNakayama (K := K) (R := R) P)
    (f : P.obj ⟶ Y) :
    fieldNakayamaHomEquiv (K := K) (R := R) P Y a f =
      ∑ i, projectiveNakayamaEvaluation (K := K) (R := R) P
        (a.hom.hom (f.hom.hom (finiteProjectiveFrameElement (R := R) P i)))
        ((projectiveHomDualFrame (R := R) P).q i) := by
  let s := ∑ i, FGModuleCat.ofHom
    (rankOne (R := R) P Y
      ((projectiveHomDualFrame (R := R) P).q i)
      (f.hom.hom (finiteProjectiveFrameElement (R := R) P i)))
  have hs : s = f :=
    categoricalRankOneFrameSum (K := K) (R := R) P Y f
  calc
    _ = fieldNakayamaHomEquiv (K := K) (R := R) P Y a s := by
      rw [hs]
    _ = ∑ i, fieldNakayamaHomEquiv (K := K) (R := R) P Y a
        (FGModuleCat.ofHom
          (rankOne (R := R) P Y
            ((projectiveHomDualFrame (R := R) P).q i)
            (f.hom.hom (finiteProjectiveFrameElement (R := R) P i)))) := by
      rw [map_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [fieldNakayamaHomEquiv_rankOne]

omit [IsNoetherianRing R] in
/-- Naturality of the field Nakayama--Hom comparison in the variable
module. -/
theorem fieldNakayamaHomEquiv_naturality
    {Y Z : FGModuleCat.{u} R} (g : Y ⟶ Z)
    (a : Z ⟶ projectiveNakayama (K := K) (R := R) P)
    (f : P.obj ⟶ Y) :
    fieldNakayamaHomEquiv (K := K) (R := R) P Y (g ≫ a) f =
      fieldNakayamaHomEquiv (K := K) (R := R) P Z a (f ≫ g) := by
  rw [fieldNakayamaHomEquiv_apply_eq_sum,
    fieldNakayamaHomEquiv_apply_eq_sum]
  rfl

include K in
omit [FiniteDimensional K R] [IsNoetherianRing R] in
/-- Precomposing a projective frame expansion by a map of projectives
transports each rank-one term along the Hom-dual map. -/
theorem categoricalRankOneProjectiveFrameSum
    {P' P : FGProjectives (R := R)} (d : P' ⟶ P)
    (Y : FGModuleCat.{u} R) (f : P.obj ⟶ Y) :
    ∑ i, FGModuleCat.ofHom
        (rankOne (R := R) P' Y
          ((projectiveHomDualMap (R := R) d).hom.hom
            ((projectiveHomDualFrame (R := R) P).q i))
          (f.hom.hom (finiteProjectiveFrameElement (R := R) P i))) =
      d.hom ≫ f := by
  apply (fgHomCarrierLinearEquiv K R P'.obj Y).injective
  rw [map_sum]
  apply LinearMap.ext
  intro p'
  change
    (∑ i, rankOne (R := R) P' Y
      ((projectiveHomDualMap (R := R) d).hom.hom
        ((projectiveHomDualFrame (R := R) P).q i))
      (f.hom.hom (finiteProjectiveFrameElement (R := R) P i))) p' =
      f.hom.hom (d.hom.hom.hom p')
  rw [LinearMap.sum_apply]
  calc
    _ = ∑ i, ((rankOne (R := R) P Y
          ((projectiveHomDualFrame (R := R) P).q i)
          (f.hom.hom (finiteProjectiveFrameElement (R := R) P i))).comp
            d.hom.hom.hom) p' := by
      apply Finset.sum_congr rfl
      intro i _
      rw [rankOne_naturality]
    _ = (∑ i, rankOne (R := R) P Y
          ((projectiveHomDualFrame (R := R) P).q i)
          (f.hom.hom (finiteProjectiveFrameElement (R := R) P i)))
            (d.hom.hom.hom p') := by
      rw [LinearMap.sum_apply]
      simp only [LinearMap.comp_apply]
    _ = f.hom.hom (d.hom.hom.hom p') := by
      rw [rankOneFrameSum]

omit [IsNoetherianRing R] in
/-- Naturality of the field Nakayama--Hom comparison in its finite
projective variable. -/
theorem fieldNakayamaHomEquiv_projectiveNaturality
    {P' P : FGProjectives (R := R)} (d : P' ⟶ P)
    (Y : FGModuleCat.{u} R)
    (a : Y ⟶ projectiveNakayama (K := K) (R := R) P')
    (f : P.obj ⟶ Y) :
    fieldNakayamaHomEquiv (K := K) (R := R) P Y
        (a ≫ (OpConjecture.Contragredient.reverseDualFunctor K R).map
          (projectiveHomDualMap (R := R) d).op) f =
      fieldNakayamaHomEquiv (K := K) (R := R) P' Y a
        (d.hom ≫ f) := by
  let s := ∑ i, FGModuleCat.ofHom
    (rankOne (R := R) P' Y
      ((projectiveHomDualMap (R := R) d).hom.hom
        ((projectiveHomDualFrame (R := R) P).q i))
      (f.hom.hom (finiteProjectiveFrameElement (R := R) P i)))
  have hs : s = d.hom ≫ f :=
    categoricalRankOneProjectiveFrameSum
      (K := K) (R := R) d Y f
  calc
    _ = ∑ i, projectiveNakayamaEvaluation (K := K) (R := R) P
        ((a ≫ (OpConjecture.Contragredient.reverseDualFunctor K R).map
          (projectiveHomDualMap (R := R) d).op).hom.hom
            (f.hom.hom (finiteProjectiveFrameElement (R := R) P i)))
        ((projectiveHomDualFrame (R := R) P).q i) :=
      fieldNakayamaHomEquiv_apply_eq_sum
        (K := K) (R := R) P Y _ f
    _ = ∑ i, projectiveNakayamaEvaluation (K := K) (R := R) P'
        (a.hom.hom (f.hom.hom (finiteProjectiveFrameElement (R := R) P i)))
        ((projectiveHomDualMap (R := R) d).hom.hom
          ((projectiveHomDualFrame (R := R) P).q i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rfl
    _ = fieldNakayamaHomEquiv (K := K) (R := R) P' Y a s := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [fieldNakayamaHomEquiv_rankOne]
    _ = fieldNakayamaHomEquiv (K := K) (R := R) P' Y a
        (d.hom ≫ f) := by rw [hs]

end FiniteProjectiveNakayama

open FiniteProjectiveNakayama

variable (K R : Type u) [Field K] [Ring R] [Algebra K R]
  [FiniteDimensional K R]
  [IsNoetherianRing R] [IsNoetherianRing Rᵐᵒᵖ]

/-- The field-valued two-step Nakayama--Matlis comparison supplied by the
ordinary finite-dimensional vector-space duality. -/
def finiteDimensionalTwoStepNakayamaMatlisComparison
    {X : FGModuleCat.{u} R}
    (T : TwoStepProjectivePresentation X) :
    TwoStepNakayamaMatlisComparison (k := K) T
      (OpConjecture.ArtinDuality.ofFiniteDimensional K) K where
  equiv₀ Y :=
    fieldNakayamaHomEquiv (K := K) (R := R) T.P₀ Y
  equiv₁ Y :=
    fieldNakayamaHomEquiv (K := K) (R := R) T.P₁ Y
  naturality₀ g a f :=
    fieldNakayamaHomEquiv_naturality
      (K := K) (R := R) T.P₀ g a f
  differential Y a f := by
    exact fieldNakayamaHomEquiv_projectiveNaturality
      (K := K) (R := R) T.projectiveDifferential Y a f

end OpConjecture.AuslanderTranspose.TwoStepProjectivePresentation
