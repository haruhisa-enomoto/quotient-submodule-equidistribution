import OpConjecture.RepresentationTheory.FullIdempotentMorita
import OpConjecture.RepresentationTheory.FiniteDimensionalRecurrence
import OpConjecture.RepresentationTheory.SingleCrossTriangularEquivalence

/-!
# Morita composition for the triangular recognition theorem

This file isolates the formal final composition.  Once a Morita basic model
has been identified with the abstract triangular algebra, its source algebra
is Morita equivalent to that algebra, or to any fixed node whose carrier is
identified with it.
-/

noncomputable section

namespace OpConjecture.MoritaTriangularRecognition

universe u

open OpConjecture.MoritaBasicizationInterface
open OpConjecture.BottomLevels.FiniteDimensionalRecurrence

/-- Recognition of the carrier of a Morita basic model gives Morita
equivalence of its source with the triangular model. -/
theorem moritaEquivalence_triangular_of_basicModel
    {K A : Type u} [Field K] [Ring A] [Algebra K A]
    (P : MoritaBasicModel (K := K) (A := A))
    (hE : Nonempty
      (OpConjecture.A2Triangular.Model K ≃ₐ[K] P.Carrier)) :
    Nonempty
      (MoritaEquivalence K A (OpConjecture.A2Triangular.Model K)) := by
  obtain ⟨E⟩ := hE
  exact ⟨MoritaEquivalence.trans K P.morita
    (MoritaEquivalence.ofAlgEquiv E).symm⟩

/-- More generally, recognition of the basic carrier as the carrier of a
fixed algebra node gives the literal node-valued Morita equivalence. -/
theorem moritaEquivalence_node_of_basicModel
    {K A : Type u} [Field K] [Ring A] [Algebra K A]
    (P : MoritaBasicModel (K := K) (A := A))
    (B : AlgebraNode K)
    (hE : Nonempty (B.Carrier ≃ₐ[K] P.Carrier)) :
    Nonempty (MoritaEquivalence K A B.Carrier) := by
  obtain ⟨E⟩ := hE
  exact ⟨MoritaEquivalence.trans K P.morita
    (MoritaEquivalence.ofAlgEquiv E).symm⟩

/-- A supplied carrier equivalence is the non-propositional specialization
of the preceding composition. -/
theorem moritaEquivalence_node_of_basicModel_algEquiv
    {K A : Type u} [Field K] [Ring A] [Algebra K A]
    (P : MoritaBasicModel (K := K) (A := A))
    (B : AlgebraNode K)
    (E : B.Carrier ≃ₐ[K] P.Carrier) :
    Nonempty (MoritaEquivalence K A B.Carrier) :=
  moritaEquivalence_node_of_basicModel P B ⟨E⟩

/-- Unconditional finite-dimensional basicization reduces triangular Morita
recognition to the same algebra-equivalence statement for every chosen basic
model. -/
theorem moritaEquivalence_triangular_of_basicization
    {K A : Type u} [Field K] [IsAlgClosed K]
    [Ring A] [Algebra K A] [FiniteDimensional K A]
    (hRecognize : ∀ P : MoritaBasicModel (K := K) (A := A),
      Nonempty (OpConjecture.A2Triangular.Model K ≃ₐ[K] P.Carrier)) :
    Nonempty
      (MoritaEquivalence K A (OpConjecture.A2Triangular.Model K)) := by
  obtain ⟨P⟩ :=
    OpConjecture.FullIdempotentMorita.finiteDimensionalMoritaBasicization
      K A
  exact moritaEquivalence_triangular_of_basicModel P (hRecognize P)

end OpConjecture.MoritaTriangularRecognition
