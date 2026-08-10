import QuotientSubmoduleEquidistribution.RepresentationTheory.SplitBasicCoordinateSystem
import Mathlib.RingTheory.SimpleModule.IsAlgClosed

/-!
# Split-basic semisimple quotients

This file derives the explicit coordinate presentation used by the Peirce
and cotangent constructions from an intrinsic split-basic hypothesis.  A
finite-dimensional algebra is split basic here when its semisimple quotient
is commutative and all maximal residue factors of that quotient are the
ground field.

Mathlib and the project foundation do not currently provide a predicate for split-basic
finite-dimensional algebras.  The definition below records exactly the
standard semisimple-quotient condition, without choosing primitive
idempotents or classifying modules.
-/

noncomputable section

namespace QuotientSubmoduleEquidistribution.SplitBasicQuotient

open QuotientSubmoduleEquidistribution.SplitBasicCoordinateSystem

universe u

/-- A finite-dimensional algebra has split-basic semisimple quotient when
the quotient is commutative and all of its maximal residue factors are
already the ground field. -/
def IsSplitBasicQuotient (K B : Type u)
    [Field K] [Ring B] [Algebra K B] : Prop :=
  ∃ hcomm : ∀ x y : B ⧸ Ring.jacobson B, x * y = y * x,
    letI : CommRing (B ⧸ Ring.jacobson B) :=
      { (inferInstance : Ring (B ⧸ Ring.jacobson B)) with
        mul_comm := hcomm }
    ∀ m : MaximalSpectrum (B ⧸ Ring.jacobson B),
      Function.Surjective
        (algebraMap K ((B ⧸ Ring.jacobson B) ⧸ m.asIdeal))

variable (K Q : Type u)
  [Field K] [CommRing Q] [Algebra K Q] [IsArtinianRing Q] [IsReduced Q]

/-- A reduced commutative Artinian algebra whose maximal residue factors
split over the ground field is a finite product of copies of that field. -/
theorem exists_algEquiv_pi_of_residueFactors_split
    (hsplit : ∀ m : MaximalSpectrum Q,
      Function.Surjective (algebraMap K (Q ⧸ m.asIdeal))) :
    ∃ n : ℕ, Nonempty (Q ≃ₐ[K] (Fin n → K)) := by
  letI : Fintype (MaximalSpectrum Q) := Fintype.ofFinite _
  letI : DecidableEq (MaximalSpectrum Q) := Classical.decEq _
  letI (m : MaximalSpectrum Q) : Field (Q ⧸ m.asIdeal) :=
    Ideal.Quotient.field m.asIdeal
  let eQ : Q ≃ₐ[K] (MaximalSpectrum Q → K) :=
    ((IsArtinianRing.equivPi Q).restrictScalars K).trans <|
      AlgEquiv.piCongrRight fun m ↦
        (AlgEquiv.ofBijective (Algebra.ofId K (Q ⧸ m.asIdeal))
          ⟨RingHom.injective _, hsplit m⟩).symm
  exact ⟨Fintype.card (MaximalSpectrum Q), ⟨
    eQ.trans <| AlgEquiv.piCongrLeft K
      (fun _ : Fin (Fintype.card (MaximalSpectrum Q)) ↦ K)
      (Fintype.equivFin (MaximalSpectrum Q))⟩⟩

variable {K B : Type u}
  [Field K] [Ring B] [Algebra K B] [FiniteDimensional K B]

/-- The split-basic quotient hypothesis supplies the explicit coordinate
datum needed by the later Peirce-corner constructions. -/
theorem exists_quotientCoordinateData_of_isSplitBasicQuotient
    (h : IsSplitBasicQuotient K B) :
    ∃ n : ℕ,
      Nonempty
        (QuotientCoordinateData (K := K) (B := B) (I := Fin n)) := by
  rcases h with ⟨hcomm, hsplit⟩
  let Q := B ⧸ Ring.jacobson B
  letI : IsArtinianRing B := IsArtinianRing.of_finite K B
  letI : CommRing Q :=
    { (inferInstance : Ring Q) with
      mul_comm := hcomm }
  letI : FiniteDimensional K Q := inferInstance
  letI : IsArtinianRing Q := IsArtinianRing.of_finite K Q
  obtain ⟨n, ⟨e⟩⟩ :=
    exists_algEquiv_pi_of_residueFactors_split K Q hsplit
  exact ⟨n, ⟨⟨e⟩⟩⟩

variable (K B : Type u)
  [Field K] [IsAlgClosed K] [Ring B] [Algebra K B]
  [FiniteDimensional K B]

/-- Over an algebraically closed field, commutativity of the semisimple
quotient implies the split-residue-factor condition. -/
theorem isSplitBasicQuotient_of_quotient_mul_comm
    (hcomm : ∀ x y : B ⧸ Ring.jacobson B, x * y = y * x) :
    IsSplitBasicQuotient K B := by
  refine ⟨hcomm, ?_⟩
  let Q := B ⧸ Ring.jacobson B
  letI : IsArtinianRing B := IsArtinianRing.of_finite K B
  letI : CommRing Q :=
    { (inferInstance : Ring Q) with
      mul_comm := hcomm }
  letI : FiniteDimensional K Q := inferInstance
  intro m
  letI : Field (Q ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
  letI : FiniteDimensional K (Q ⧸ m.asIdeal) := inferInstance
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral.2

/-- Over an algebraically closed field, commutativity of the semisimple
quotient is enough to obtain split-basic coordinates. -/
theorem exists_quotientCoordinateData_of_quotient_mul_comm
    (hcomm : ∀ x y : B ⧸ Ring.jacobson B, x * y = y * x) :
    ∃ n : ℕ,
      Nonempty
        (QuotientCoordinateData (K := K) (B := B) (I := Fin n)) := by
  exact exists_quotientCoordinateData_of_isSplitBasicQuotient
    (isSplitBasicQuotient_of_quotient_mul_comm K B hcomm)

end QuotientSubmoduleEquidistribution.SplitBasicQuotient
