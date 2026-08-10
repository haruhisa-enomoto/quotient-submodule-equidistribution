import QuotientSubmoduleEquidistribution.RepresentationTheory.FiniteProjectiveNakayamaPairing

/-!
# Finite-projective Nakayama--Hom equivalence

Over a field, the rank-one pairing identifies `Hom(Y,DQ)` with the linear
dual of `Hom(P,Y)` for every finitely generated projective `P`.  A chosen
finite dual frame supplies explicit injectivity and surjectivity proofs.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ModuleCat.Algebra

namespace QuotientSubmoduleEquidistribution.AuslanderTranspose.TwoStepProjectivePresentation

open QuotientSubmoduleEquidistribution.RingelStable

universe u

namespace FiniteProjectiveNakayama

variable (K R : Type u) [Field K] [Ring R] [Algebra K R]
  [FiniteDimensional K R]
  [IsNoetherianRing R] [IsNoetherianRing Rᵐᵒᵖ]

variable (P : FGProjectives (R := R))

def projectiveNakayamaEvaluation
    (z : projectiveNakayama (K := K) (R := R) P)
    (q : (projectiveHomDual (R := R) P).obj) : K := by
  change Module.Dual K (projectiveHomDual (R := R) P).obj at z
  exact z q

omit [IsNoetherianRing R] in
@[simp]
theorem projectiveNakayamaEvaluation_add
    (z z' : projectiveNakayama (K := K) (R := R) P)
    (q : (projectiveHomDual (R := R) P).obj) :
    projectiveNakayamaEvaluation (K := K) (R := R) P (z + z') q =
      projectiveNakayamaEvaluation (K := K) (R := R) P z q +
        projectiveNakayamaEvaluation (K := K) (R := R) P z' q :=
  rfl

omit [IsNoetherianRing R] in
@[simp]
theorem projectiveNakayamaEvaluation_smul
    (r : R) (z : projectiveNakayama (K := K) (R := R) P)
    (q : (projectiveHomDual (R := R) P).obj) :
    projectiveNakayamaEvaluation (K := K) (R := R) P (r • z) q =
      projectiveNakayamaEvaluation (K := K) (R := R) P z (MulOpposite.op r • q) :=
  rfl

omit [IsNoetherianRing R] in
@[simp]
theorem projectiveNakayamaEvaluation_ksmul
    (k : K) (z : projectiveNakayama (K := K) (R := R) P)
    (q : (projectiveHomDual (R := R) P).obj) :
    projectiveNakayamaEvaluation (K := K) (R := R) P (k • z) q =
      k * projectiveNakayamaEvaluation (K := K) (R := R) P z q :=
  congrArg (fun ell ↦ ell q)
    ((QuotientSubmoduleEquidistribution.Contragredient.reverseInnerDualEquiv K R
      (projectiveHomDual (R := R) P).obj).map_smul k z)

omit [IsNoetherianRing R] in
theorem projectiveNakayamaEvaluation_sum
    {n : ℕ}
    (z : projectiveNakayama (K := K) (R := R) P)
    (v : Fin n → (projectiveHomDual (R := R) P).obj) :
    projectiveNakayamaEvaluation (K := K) (R := R) P z (∑ i, v i) =
      ∑ i, projectiveNakayamaEvaluation (K := K) (R := R) P z (v i) := by
  change
    (show Module.Dual K (projectiveHomDual (R := R) P).obj from z) (∑ i, v i) =
      ∑ i, (show Module.Dual K (projectiveHomDual (R := R) P).obj from z) (v i)
  rw [map_sum]

omit [IsNoetherianRing R] in
theorem rankOneFrameSum
    (Y : FGModuleCat.{u} R) (f : P.obj →ₗ[R] Y) :
    ∑ i,
        rankOne (R := R) P Y
          ((projectiveHomDualFrame (R := R) P).q i)
          (f (finiteProjectiveFrameElement (R := R) P i)) =
      f := by
  apply LinearMap.ext
  intro p
  rw [LinearMap.sum_apply]
  change
    (∑ i,
      MulOpposite.unop
          (counitEvaluation (R := R) P p
            ((projectiveHomDualFrame (R := R) P).q i)) •
        f (finiteProjectiveFrameElement (R := R) P i)) = f p
  have h := congrArg (fun z ↦ f z) (finiteProjectiveFrameReconstruction (R := R) P p)
  simpa only [map_sum, map_smul] using h

omit [IsNoetherianRing R] in
theorem nakayamaHomLinearMap_injective
    (Y : FGModuleCat.{u} R) :
    Function.Injective (nakayamaHomLinearMap (K := K) (R := R) P Y) := by
  intro ell mu h
  apply LinearMap.ext
  intro f
  have hf := rankOneFrameSum (R := R) P Y f
  rw [← hf, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hy := LinearMap.congr_fun h
    (f (finiteProjectiveFrameElement (R := R) P i))
  have hq := LinearMap.congr_fun hy
    ((projectiveHomDualFrame (R := R) P).q i)
  exact hq

def nakayamaHomInverseValue
    (Y : FGModuleCat.{u} R)
    (g : Y →ₗ[R] projectiveNakayama (K := K) (R := R) P)
    (f : P.obj →ₗ[R] Y) : K :=
  ∑ i, projectiveNakayamaEvaluation (K := K) (R := R) P
    (g (f (finiteProjectiveFrameElement (R := R) P i)))
    ((projectiveHomDualFrame (R := R) P).q i)

def nakayamaHomInverseFunctional
    (Y : FGModuleCat.{u} R)
    (g : Y →ₗ[R] projectiveNakayama (K := K) (R := R) P) :
    Module.Dual K (P.obj →ₗ[R] Y) where
  toFun := nakayamaHomInverseValue (K := K) (R := R) P Y g
  map_add' f f' := by
    simp [nakayamaHomInverseValue, Finset.sum_add_distrib]
  map_smul' k f := by
    rw [nakayamaHomInverseValue, nakayamaHomInverseValue]
    change
      (∑ i, projectiveNakayamaEvaluation (K := K) (R := R) P
        (g ((k • f) (finiteProjectiveFrameElement (R := R) P i)))
        ((projectiveHomDualFrame (R := R) P).q i)) =
        k * ∑ i, projectiveNakayamaEvaluation (K := K) (R := R) P
          (g (f (finiteProjectiveFrameElement (R := R) P i)))
          ((projectiveHomDualFrame (R := R) P).q i)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [LinearMap.smul_apply]
    have hg := (g.restrictScalars K).map_smul k
      (f (finiteProjectiveFrameElement (R := R) P i))
    change
      g (k • f (finiteProjectiveFrameElement (R := R) P i)) =
        k • g (f (finiteProjectiveFrameElement (R := R) P i)) at hg
    rw [hg, projectiveNakayamaEvaluation_ksmul]

omit [IsNoetherianRing R] in
theorem nakayamaHomLinearMap_surjective
    (Y : FGModuleCat.{u} R) :
    Function.Surjective (nakayamaHomLinearMap (K := K) (R := R) P Y) := by
  intro g
  refine ⟨nakayamaHomInverseFunctional (K := K) (R := R) P Y g, ?_⟩
  apply LinearMap.ext
  intro y
  apply LinearMap.ext
  intro q
  change
    (∑ i,
      projectiveNakayamaEvaluation (K := K) (R := R) P
        (g
          (rankOne (R := R) P Y q y
            (finiteProjectiveFrameElement (R := R) P i)))
        ((projectiveHomDualFrame (R := R) P).q i)) =
      projectiveNakayamaEvaluation (K := K) (R := R) P (g y) q
  calc
    _ = ∑ i, projectiveNakayamaEvaluation (K := K) (R := R) P (g y)
        (((projectiveHomDualFrame (R := R) P).phi i q) •
          (projectiveHomDualFrame (R := R) P).q i) := by
      apply Finset.sum_congr rfl
      intro i hi
      change
        projectiveNakayamaEvaluation (K := K) (R := R) P
          (g
            (MulOpposite.unop
              (counitEvaluation (R := R) P
                (finiteProjectiveFrameElement (R := R) P i) q) • y))
          ((projectiveHomDualFrame (R := R) P).q i) = _
      rw [g.map_smul]
      rw [projectiveNakayamaEvaluation_smul]
      rw [MulOpposite.op_unop]
      rw [show
        counitEvaluation (R := R) P
            (finiteProjectiveFrameElement (R := R) P i) =
          (projectiveHomDualFrame (R := R) P).phi i by
            exact counitEvaluation_frameElement (R := R) P i]
    _ = projectiveNakayamaEvaluation (K := K) (R := R) P (g y)
        (∑ i, ((projectiveHomDualFrame (R := R) P).phi i q) •
          (projectiveHomDualFrame (R := R) P).q i) := by
      rw [projectiveNakayamaEvaluation_sum]
    _ = projectiveNakayamaEvaluation (K := K) (R := R) P (g y) q := by
      rw [(projectiveHomDualFrame (R := R) P).total]

omit [IsNoetherianRing R] in
theorem nakayamaHomLinearMap_bijective
    (Y : FGModuleCat.{u} R) :
    Function.Bijective (nakayamaHomLinearMap (K := K) (R := R) P Y) :=
  ⟨nakayamaHomLinearMap_injective (K := K) (R := R) P Y,
    nakayamaHomLinearMap_surjective (K := K) (R := R) P Y⟩

end FiniteProjectiveNakayama

end QuotientSubmoduleEquidistribution.AuslanderTranspose.TwoStepProjectivePresentation
