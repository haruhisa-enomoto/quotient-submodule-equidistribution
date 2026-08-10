import OpConjecture.RepresentationTheory.ConnectedSmallCoreExceptionalArrowSupport
import OpConjecture.RepresentationTheory.FamilyFourControl
import OpConjecture.RepresentationTheory.OneSimpleNakayamaReduction

/-!
# The exact loop-free Nakayama reduction

The standard representation-theoretic theorem still needed says that a
finite-dimensional algebra whose multiplicity-bearing Ext-Gabriel quiver has
at most one arrow leaving and at most one arrow entering every vertex is a
Nakayama algebra.  The first definition records exactly that theorem in the
language already used by the project.  The results below prove that the
loop-free two-vertex exceptional support supplies both degree hypotheses.

The classification theorem is kept as an explicit interface below; this file
does not postulate it as an axiom.
-/

noncomputable section

namespace OpConjecture.NoLoopNakayamaReduction

open OpConjecture.GabrielArrowBridge
open OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore

universe u v

/-- A reusable module-theoretic step already within reach of the current
library: a simple top and a uniserial radical make the whole module
uniserial.  Thus a future Gabriel proof may work by showing that successive
radicals of the indecomposable projectives have simple (or zero) top. -/
theorem isUniserialModule_of_simpleTop_of_radicalUniserial
    {R : Type u} [Ring R]
    {M : Type v} [AddCommGroup M] [Module R M] [IsNoetherian R M]
    (hTop : IsSimpleModule R (M ⧸ Module.jacobson R M))
    (hRadical :
      OpConjecture.IsUniserialModule R (Module.jacobson R M)) :
    OpConjecture.IsUniserialModule R M := by
  let J : Submodule R M := Module.jacobson R M
  unfold OpConjecture.IsUniserialModule at hRadical ⊢
  constructor
  intro P Q
  by_cases hPTop : P = ⊤
  · right
    simp [hPTop]
  by_cases hQTop : Q = ⊤
  · left
    simp [hQTop]
  have hPJ : P ≤ J :=
    OpConjecture.FamilyFourControl.le_jacobson_of_ne_top_of_simple_top
      hTop hPTop
  have hQJ : Q ≤ J :=
    OpConjecture.FamilyFourControl.le_jacobson_of_ne_top_of_simple_top
      hTop hQTop
  let P' : Submodule R J := Submodule.comap J.subtype P
  let Q' : Submodule R J := Submodule.comap J.subtype Q
  have hPMap : Submodule.map J.subtype P' = P := by
    dsimp only [P']
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hPJ]
  have hQMap : Submodule.map J.subtype Q' = Q := by
    dsimp only [Q']
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hQJ]
  rcases hRadical.total P' Q' with hPQ | hQP
  · left
    rw [← hPMap, ← hQMap]
    exact Submodule.map_mono hPQ
  · right
    rw [← hPMap, ← hQMap]
    exact Submodule.map_mono hQP

variable {K A : Type u}
  [Field K] [IsAlgClosed K]
  [Ring A] [Small.{u} A] [IsNoetherianRing A] [IsArtinianRing A]
  [Algebra K A]
  {ι : Type v} [Finite ι]
  (σ : OpConjecture.IndecomposableSkeleton.{u, v, u} A ι)

/-- The exact general classification theorem needed after the finite-support
argument: one outgoing and one incoming multiplicity-bearing Ext-Gabriel
arrow at most force every indecomposable representative to be uniserial. -/
def ExtGabrielInOutDegreeOneNakayamaClassification : Prop :=
  NoParallelExtSupport (K := K) σ →
    Function.Injective (ExtGabrielArrowIndex.source (K := K) σ) →
    Function.Injective (ExtGabrielArrowIndex.target (K := K) σ) →
      OpConjecture.LocalNakayamaBranch.IsNakayamaSkeleton σ

omit [IsAlgClosed K] [IsArtinianRing A] [Finite ι] in
/-- A loop-free relabelled two-vertex support makes the original Ext-arrow
source map injective. -/
theorem extSource_injective_of_twoVertexSupport_noLoops
    (D : ExceptionalExtGabrielArrowIdealData.Data (K := K) σ)
    (e : σ.SimpleIndex ≃ Fin 2)
    (hNoParallel : NoParallelExtSupport (K := K) σ)
    (hNoLoops :
      (ExceptionalExtGabrielArrowIdealData.twoVertexSupport
        σ D e hNoParallel).NoLoops) :
    Function.Injective (ExtGabrielArrowIndex.source (K := K) σ) := by
  intro a b hab
  apply
    (ExceptionalExtGabrielArrowIdealData.twoVertexSupport
      σ D e hNoParallel).source_injective_of_noLoops hNoLoops
  exact congrArg e hab

omit [IsAlgClosed K] [IsArtinianRing A] [Finite ι] in
/-- A loop-free relabelled two-vertex support makes the original Ext-arrow
target map injective. -/
theorem extTarget_injective_of_twoVertexSupport_noLoops
    (D : ExceptionalExtGabrielArrowIdealData.Data (K := K) σ)
    (e : σ.SimpleIndex ≃ Fin 2)
    (hNoParallel : NoParallelExtSupport (K := K) σ)
    (hNoLoops :
      (ExceptionalExtGabrielArrowIdealData.twoVertexSupport
        σ D e hNoParallel).NoLoops) :
    Function.Injective (ExtGabrielArrowIndex.target (K := K) σ) := by
  intro a b hab
  apply
    (ExceptionalExtGabrielArrowIdealData.twoVertexSupport
      σ D e hNoParallel).target_injective_of_noLoops hNoLoops
  exact congrArg e hab

omit [IsAlgClosed K] [IsArtinianRing A] [Finite ι] in
/-- The complete formal adapter: after the standard Ext-quiver degree
classification theorem is supplied, the loop-free exceptional branch is
Nakayama.  No further exceptional-core or arrow-ideal argument is needed at
this point. -/
theorem isNakayamaSkeleton_of_twoVertexSupport_noLoops
    (hClassification :
      ExtGabrielInOutDegreeOneNakayamaClassification (K := K) σ)
    (D : ExceptionalExtGabrielArrowIdealData.Data (K := K) σ)
    (e : σ.SimpleIndex ≃ Fin 2)
    (hNoParallel : NoParallelExtSupport (K := K) σ)
    (hNoLoops :
      (ExceptionalExtGabrielArrowIdealData.twoVertexSupport
        σ D e hNoParallel).NoLoops) :
    OpConjecture.LocalNakayamaBranch.IsNakayamaSkeleton σ :=
  hClassification
    hNoParallel
    (extSource_injective_of_twoVertexSupport_noLoops
      σ D e hNoParallel hNoLoops)
    (extTarget_injective_of_twoVertexSupport_noLoops
      σ D e hNoParallel hNoLoops)

end OpConjecture.NoLoopNakayamaReduction
