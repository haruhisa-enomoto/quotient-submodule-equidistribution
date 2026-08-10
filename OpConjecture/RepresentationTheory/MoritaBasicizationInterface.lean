import OpConjecture.RepresentationTheory.BasicnessWrapper
import OpConjecture.RepresentationTheory.MoritaConventionBridge
import Mathlib.RingTheory.Idempotents

/-!
# Full-idempotent interface for Morita basicization

This file states the interface used by the classical existence theorem.  It
separates its two ring-theoretic and categorical inputs:

* existence of a full idempotent whose corner is basic; and
* the full-idempotent Morita theorem.

Everything after those inputs, including finite dimensionality of the
corner and construction of split quotient coordinates, is proved here.
-/

noncomputable section

namespace OpConjecture.MoritaBasicizationInterface

universe u

variable {K A : Type u}
  [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]

/-- The standard elementwise formulation of fullness: `1` is a finite sum
of terms `a * e * b`, equivalently `AeA = A`.  Mathlib's `Ideal` is a
one-sided notion over a noncommutative ring, so `Ideal.span {e} = top` would
not be the correct definition here. -/
def IsFullElem (e : A) : Prop :=
  ∃ (n : ℕ) (a b : Fin n → A),
    ∑ i, a i * e * b i = 1

section CornerAlgebra

variable {e : A} (he : IsIdempotentElem e)

/-- The canonical scalar map into the idempotent corner `eAe`, sending
`k` to `(k · 1_A)e`. -/
def cornerAlgebraMap : K →+* he.Corner where
  toFun k := ⟨algebraMap K A k * e, by
    apply (Subsemigroup.mem_corner_iff he).2
    constructor
    · calc
        e * (algebraMap K A k * e) =
            (e * algebraMap K A k) * e := by rw [mul_assoc]
        _ = (algebraMap K A k * e) * e := by
              rw [Algebra.commutes k e]
        _ = algebraMap K A k * (e * e) := by rw [mul_assoc]
        _ = algebraMap K A k * e := by rw [he.eq]
    · calc
        algebraMap K A k * e * e =
            algebraMap K A k * (e * e) := by rw [mul_assoc]
        _ = algebraMap K A k * e := by rw [he.eq]
    ⟩
  map_one' := by
    apply Subtype.ext
    change algebraMap K A 1 * e = e
    simp
  map_mul' k l := by
    apply Subtype.ext
    change
      algebraMap K A (k * l) * e =
        (algebraMap K A k * e) * (algebraMap K A l * e)
    calc
      algebraMap K A (k * l) * e =
          (algebraMap K A k * algebraMap K A l) * e := by rw [map_mul]
      _ = algebraMap K A k * (algebraMap K A l * e) := by
            rw [mul_assoc]
      _ = algebraMap K A k *
          (e * (algebraMap K A l * e)) := by
            congr 1
            calc
              algebraMap K A l * e =
                  (algebraMap K A l * e) * e := by rw [mul_assoc, he.eq]
              _ = (e * algebraMap K A l) * e := by
                    rw [Algebra.commutes l e]
              _ = e * (algebraMap K A l * e) := by rw [mul_assoc]
      _ = (algebraMap K A k * e) *
          (algebraMap K A l * e) := by rw [mul_assoc]
  map_zero' := by
    apply Subtype.ext
    change algebraMap K A 0 * e = 0
    simp
  map_add' k l := by
    apply Subtype.ext
    change
      algebraMap K A (k + l) * e =
        algebraMap K A k * e + algebraMap K A l * e
    simp [add_mul]

/-- The canonical `K`-algebra structure on `eAe`. -/
@[reducible] def cornerAlgebra : Algebra K he.Corner :=
  (cornerAlgebraMap (K := K) he).toAlgebra' <| by
    intro k x
    apply Subtype.ext
    have hx := (Subsemigroup.mem_corner_iff he).1 x.property
    change
      (algebraMap K A k * e) * x.1 =
        x.1 * (algebraMap K A k * e)
    calc
      (algebraMap K A k * e) * x.1 =
          algebraMap K A k * (e * x.1) := by rw [mul_assoc]
      _ = algebraMap K A k * x.1 := by rw [hx.1]
      _ = x.1 * algebraMap K A k := Algebra.commutes k x.1
      _ = (x.1 * e) * algebraMap K A k := by rw [hx.2]
      _ = x.1 * (e * algebraMap K A k) := by rw [mul_assoc]
      _ = x.1 * (algebraMap K A k * e) := by
        rw [Algebra.commutes k e]

/-- Inclusion of a corner into the ambient algebra is `K`-linear for the
canonical corner algebra structure. -/
def cornerInclusionLinearMap :
    letI : Algebra K he.Corner := cornerAlgebra (K := K) he
    he.Corner →ₗ[K] A := by
  letI : Algebra K he.Corner := cornerAlgebra (K := K) he
  exact
    { toFun := fun x ↦ x.1
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun k x ↦ by
        have hx := (Subsemigroup.mem_corner_iff he).1 x.property
        change (algebraMap K A k * e) * x.1 = k • x.1
        rw [mul_assoc, hx.1, Algebra.smul_def] }

/-- A corner of a finite-dimensional algebra is finite-dimensional over the
same ground field. -/
theorem cornerFiniteDimensional :
    letI : Algebra K he.Corner := cornerAlgebra (K := K) he
    FiniteDimensional K he.Corner := by
  letI : Algebra K he.Corner := cornerAlgebra (K := K) he
  exact FiniteDimensional.of_injective
    (cornerInclusionLinearMap (K := K) he)
    Subtype.val_injective

end CornerAlgebra

/-- The ring-theoretic half of classical basicization: a full idempotent
whose corner is basic in the conventional reduced-semisimple-quotient
sense. -/
structure BasicizingFullIdempotent where
  e : A
  idem : IsIdempotentElem e
  full : IsFullElem e
  basic :
    letI : Algebra K idem.Corner := cornerAlgebra (K := K) idem
    letI : FiniteDimensional K idem.Corner :=
      cornerFiniteDimensional (K := K) idem
    OpConjecture.BasicnessWrapper.IsBasicAlgebra K idem.Corner

/-- The exact categorical theorem absent from Mathlib's current Morita API:
a full idempotent induces a Morita equivalence with its corner. -/
def FullIdempotentMoritaBridge : Prop :=
  ∀ (e : A) (he : IsIdempotentElem e), IsFullElem e →
    letI : Algebra K he.Corner := cornerAlgebra (K := K) he
    Nonempty (MoritaEquivalence K A he.Corner)

/-- Paper-facing conventional basicization data, without committing
downstream files to a particular construction of the basic algebra. -/
structure MoritaBasicModel where
  Carrier : Type u
  [ring : Ring Carrier]
  [algebra : Algebra K Carrier]
  [finiteDimensional : FiniteDimensional K Carrier]
  morita : MoritaEquivalence K A Carrier
  basic : OpConjecture.BasicnessWrapper.IsBasicAlgebra K Carrier

namespace MoritaBasicModel

attribute [instance] ring algebra finiteDimensional

/-- A full-idempotent witness and the general Morita bridge produce
the exact model needed by the maintained split-basic quotient wrapper. -/
def ofBasicizingFullIdempotent
    (hbridge : FullIdempotentMoritaBridge (K := K) (A := A))
    (P : BasicizingFullIdempotent (K := K) (A := A)) :
    MoritaBasicModel (K := K) (A := A) := by
  letI : Algebra K P.idem.Corner := cornerAlgebra (K := K) P.idem
  letI : FiniteDimensional K P.idem.Corner :=
    cornerFiniteDimensional (K := K) P.idem
  exact
    { Carrier := P.idem.Corner
      morita := (hbridge P.e P.idem P.full).some
      basic := P.basic }

variable [IsAlgClosed K]

omit [FiniteDimensional K A] in
/-- The model's target has the intrinsic split-basic quotient property. -/
theorem target_isSplitBasicQuotient
    (P : MoritaBasicModel (K := K) (A := A)) :
    OpConjecture.SplitBasicQuotient.IsSplitBasicQuotient K P.Carrier :=
  OpConjecture.BasicnessWrapper.isSplitBasicQuotient_of_isBasicAlgebra
    K P.Carrier P.basic

omit [FiniteDimensional K A] in
/-- Thus conventional Morita basicization closes the current explicit
coordinate seam: the target quotient is a finite product of copies of `K`. -/
theorem exists_target_quotientCoordinateData
    (P : MoritaBasicModel (K := K) (A := A)) :
    ∃ n : ℕ,
      Nonempty
        (OpConjecture.SplitBasicCoordinateSystem.QuotientCoordinateData
          (K := K) (B := P.Carrier) (I := Fin n)) :=
  OpConjecture.BasicnessWrapper.exists_quotientCoordinateData_of_isBasicAlgebra
    K P.Carrier P.basic

/-- The same model simultaneously provides the right-module equivalence
needed to transport all OP level data back to the source algebra. -/
def rightFgEquivalence
    (P : MoritaBasicModel (K := K) (A := A)) :
    FGModuleCat.{u} Aᵐᵒᵖ ≌ FGModuleCat.{u} P.Carrierᵐᵒᵖ :=
  OpConjecture.MoritaConventionBridge.rightFgEquivalence
    K A P.Carrier P.morita

end MoritaBasicModel

/-- Paper-facing conventional basicization theorem, separated from all
downstream coordinate and Morita-invariance arguments. -/
def FiniteDimensionalMoritaBasicization
    (K : Type u) [Field K] : Prop :=
  ∀ (A : Type u) [Ring A] [Algebra K A] [FiniteDimensional K A],
    Nonempty (MoritaBasicModel (K := K) (A := A))

end OpConjecture.MoritaBasicizationInterface
