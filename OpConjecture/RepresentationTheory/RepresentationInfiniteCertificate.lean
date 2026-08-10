import Mathlib.Data.Fintype.Pigeonhole
import OpConjecture.RepresentationTheory.FiniteType

/-!
# Infinite indecomposable-family certificates

One infinite, pairwise nonisomorphic family of indecomposable modules is
enough to contradict the existence of a finite complete indecomposable
skeleton.  No classification of all modules is required.
-/

noncomputable section

open CategoryTheory

namespace OpConjecture.RepresentationInfiniteCertificate

universe u v z

variable {R : Type u} [Ring R] [IsNoetherianRing R]

/-- An explicit infinite family of pairwise nonisomorphic finitely generated
indecomposable modules. -/
structure InfiniteIndecomposableFamily (Parameter : Type z) where
  obj : Parameter → FGModuleCat.{u} R
  indecomposable : ∀ a, OpConjecture.Foundation.IsIndecomposableModule R (obj a)
  eq_of_iso : ∀ {a b}, Nonempty (obj a ≅ obj b) → a = b

namespace InfiniteIndecomposableFamily

variable {Parameter : Type z} [Infinite Parameter]

/-- A finite complete indecomposable skeleton cannot coexist with an explicit
infinite pairwise-nonisomorphic indecomposable family. -/
theorem false_of_finite_skeleton
    (F : InfiniteIndecomposableFamily (R := R) Parameter)
    {ι : Type v} [Finite ι]
    (σ : OpConjecture.IndecomposableSkeleton.{u, v, u} R ι) :
    False := by
  let index : Parameter → ι := fun a ↦
    (σ.complete (F.obj a) (F.indecomposable a)).choose
  let toRep (a : Parameter) :
      F.obj a ≅ σ.obj (index a) :=
    (σ.complete (F.obj a) (F.indecomposable a)).choose_spec.some
  obtain ⟨a, b, hab, habIndex⟩ :=
    Finite.exists_ne_map_eq_of_infinite index
  have toRepB : F.obj b ≅ σ.obj (index a) := by
    simpa [habIndex] using toRep b
  exact hab <| F.eq_of_iso ⟨(toRep a).trans toRepB.symm⟩

/-- The same obstruction against the repository's bundled finite-skeleton
interface. -/
theorem false_of_bundled_finite_skeleton
    (F : InfiniteIndecomposableFamily (R := R) Parameter)
    (σ : OpConjecture.FiniteIndecomposableSkeleton.{u, v, u} R) :
    False := by
  letI : Finite σ.ι := σ.finite_ι
  exact F.false_of_finite_skeleton σ.skeleton

end InfiniteIndecomposableFamily

end OpConjecture.RepresentationInfiniteCertificate
