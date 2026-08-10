import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Radical-square-zero weighted enumeration

This file formalizes the finite combinatorial tail of the
radical-square-zero argument.  Its input is a common finite family of
nonsimple closed cores, a size statistic, and a top-support statistic.
No separated-representation or module-classification theorem is assumed.

For a fixed core, the `A` side may freely choose simple labels outside
the mandatory top support.  The separated-quiver `B` side has one
additional independent choice among all simple labels.  Consequently its
enumerator is the `A` enumerator multiplied by `(1 + X)^v`.
-/

namespace OpConjecture.RadicalSquareZeroCombinatorics

open Finset Polynomial
open scoped BigOperators

universe u v

/-- Abstract data remaining after the representation-theoretic reduction:
a common core family, a core-size statistic, and a top-support statistic. -/
structure CoreFamily (Core : Type u) (Vertex : Type v) where
  coreSize : Core → ℕ
  topSupport : Core → Finset Vertex

variable {Core : Type u} {Vertex : Type v}
  [Fintype Vertex] [DecidableEq Vertex]

namespace CoreFamily

/-- The simple labels outside the mandatory top support of a core. -/
abbrev FreeVertex (F : CoreFamily Core Vertex) (x : Core) :=
  ↥(F.topSupport x)ᶜ

/-- An `A` decoration chooses any subset of the nonmandatory simple
labels. -/
abbrev AChoice (F : CoreFamily Core Vertex) (x : Core) :=
  Finset (FreeVertex F x)

/-- A `B` decoration consists of an `A` decoration together with an
independent subset of all simple labels. -/
abbrev BChoice (F : CoreFamily Core Vertex) (x : Core) :=
  AChoice F x × Finset Vertex

/-- The number of optional `A`-side simple labels is `v - |T(x)|`. -/
theorem card_freeVertex (F : CoreFamily Core Vertex) (x : Core) :
    Fintype.card (F.FreeVertex x) =
      Fintype.card Vertex - (F.topSupport x).card := by
  calc
    Fintype.card (F.FreeVertex x) = ((F.topSupport x)ᶜ).card :=
      Fintype.card_coe _
    _ = Fintype.card Vertex - (F.topSupport x).card :=
      Finset.card_compl _

/-- The common mandatory contribution of a core and its top support. -/
def baseWeight (F : CoreFamily Core Vertex) (x : Core) : ℕ :=
  F.coreSize x + (F.topSupport x).card

/-- Weight of an `A` decoration. -/
def aWeight (F : CoreFamily Core Vertex) (x : Core)
    (s : AChoice F x) : ℕ :=
  F.baseWeight x + s.card

/-- Weight of a `B` decoration. -/
def bWeight (F : CoreFamily Core Vertex) (x : Core)
    (s : BChoice F x) : ℕ :=
  F.baseWeight x + s.1.card + s.2.card

/-- The weighted enumerator of all subsets of a finite type. -/
theorem simpleChoiceEnumerator (α : Type*) [Fintype α] :
    (∑ s : Finset α, X ^ s.card : ℕ[X]) =
      (1 + X) ^ Fintype.card α := by
  classical
  rw [← Finset.powerset_univ]
  calc
    (∑ s ∈ (Finset.univ : Finset α).powerset, X ^ s.card : ℕ[X]) =
        ∑ s ∈ (Finset.univ : Finset α).powerset,
          ∏ _i ∈ s, (X : ℕ[X]) := by
      apply Finset.sum_congr rfl
      intro s _
      simp
    _ = ∏ i ∈ (Finset.univ : Finset α), (1 + (X : ℕ[X])) :=
      (Finset.prod_one_add (f := fun _ : α ↦ (X : ℕ[X]))
        Finset.univ).symm
    _ = (1 + X) ^ Fintype.card α := by simp

/-- Enumerator of the decorations over one core on the `A` side. -/
noncomputable def aCoreEnumerator
    (F : CoreFamily Core Vertex) (x : Core) : ℕ[X] :=
  ∑ s : AChoice F x, X ^ F.aWeight x s

/-- Enumerator of the decorations over one core on the `B` side. -/
noncomputable def bCoreEnumerator
    (F : CoreFamily Core Vertex) (x : Core) : ℕ[X] :=
  ∑ s : BChoice F x, X ^ F.bWeight x s

/-- The `A` fiber has its mandatory factor and one Boolean choice for
each simple label outside the top support. -/
theorem aCoreEnumerator_eq
    (F : CoreFamily Core Vertex) (x : Core) :
    F.aCoreEnumerator x =
      X ^ F.baseWeight x *
        (1 + X) ^ (Fintype.card Vertex - (F.topSupport x).card) := by
  classical
  unfold aCoreEnumerator aWeight
  simp_rw [pow_add]
  rw [← Finset.mul_sum]
  rw [simpleChoiceEnumerator]
  rw [card_freeVertex]

/-- Per core, the additional independent simple choice on the `B` side
contributes exactly `(1 + X)^v`. -/
theorem bCoreEnumerator_eq_aCoreEnumerator_mul
    (F : CoreFamily Core Vertex) (x : Core) :
    F.bCoreEnumerator x =
      F.aCoreEnumerator x * (1 + X) ^ Fintype.card Vertex := by
  classical
  unfold bCoreEnumerator aCoreEnumerator bWeight aWeight
  rw [Fintype.sum_prod_type]
  simp_rw [pow_add]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  rw [← Finset.mul_sum, simpleChoiceEnumerator]

/-- Equivalent closed form for a `B` fiber, matching the manuscript
exponent `2v - |T(x)|`. -/
theorem bCoreEnumerator_eq
    (F : CoreFamily Core Vertex) (x : Core) :
    F.bCoreEnumerator x =
      X ^ F.baseWeight x *
        (1 + X) ^ (2 * Fintype.card Vertex - (F.topSupport x).card) := by
  rw [bCoreEnumerator_eq_aCoreEnumerator_mul,
    aCoreEnumerator_eq, mul_assoc, ← pow_add]
  congr 2
  have htop :
      (F.topSupport x).card ≤ Fintype.card Vertex :=
    Finset.card_le_univ _
  omega

section FullEnumerator

variable [Fintype Core]

/-- The full `A` enumerator, summed over the shared finite core family. -/
noncomputable def aEnumerator (F : CoreFamily Core Vertex) : ℕ[X] :=
  ∑ x : Core, F.aCoreEnumerator x

/-- The full `B` enumerator, summed over the same finite core family. -/
noncomputable def bEnumerator (F : CoreFamily Core Vertex) : ℕ[X] :=
  ∑ x : Core, F.bCoreEnumerator x

/-- Main multiplication identity.  It deliberately avoids polynomial
division. -/
theorem bEnumerator_eq_aEnumerator_mul
    (F : CoreFamily Core Vertex) :
    F.bEnumerator =
      F.aEnumerator * (1 + X) ^ Fintype.card Vertex := by
  classical
  unfold bEnumerator aEnumerator
  simp_rw [bCoreEnumerator_eq_aCoreEnumerator_mul]
  rw [Finset.sum_mul]

/-- Sum form of the manuscript's `A` expression. -/
theorem aEnumerator_eq_sum_closedForm
    (F : CoreFamily Core Vertex) :
    F.aEnumerator =
      ∑ x : Core,
        X ^ (F.coreSize x + (F.topSupport x).card) *
          (1 + X) ^
            (Fintype.card Vertex - (F.topSupport x).card) := by
  classical
  unfold aEnumerator
  apply Finset.sum_congr rfl
  intro x _
  simpa [baseWeight] using aCoreEnumerator_eq F x

/-- Sum form of the manuscript's `B` expression. -/
theorem bEnumerator_eq_sum_closedForm
    (F : CoreFamily Core Vertex) :
    F.bEnumerator =
      ∑ x : Core,
        X ^ (F.coreSize x + (F.topSupport x).card) *
          (1 + X) ^
            (2 * Fintype.card Vertex - (F.topSupport x).card) := by
  classical
  unfold bEnumerator
  apply Finset.sum_congr rfl
  intro x _
  simpa [baseWeight] using bCoreEnumerator_eq F x

/-- The manuscript-shaped finite identity, stated without polynomial
division or names for the two enumerators. -/
theorem sum_closedForm_B_eq_sum_closedForm_A_mul
    (F : CoreFamily Core Vertex) :
    (∑ x : Core,
        (X : ℕ[X]) ^ (F.coreSize x + (F.topSupport x).card) *
          (1 + X) ^
            (2 * Fintype.card Vertex - (F.topSupport x).card)) =
      (∑ x : Core,
          X ^ (F.coreSize x + (F.topSupport x).card) *
            (1 + X) ^
              (Fintype.card Vertex - (F.topSupport x).card)) *
        (1 + X) ^ Fintype.card Vertex := by
  rw [← bEnumerator_eq_sum_closedForm,
    ← aEnumerator_eq_sum_closedForm]
  exact bEnumerator_eq_aEnumerator_mul F

end FullEnumerator

end CoreFamily

end OpConjecture.RadicalSquareZeroCombinatorics
