import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Lex
import Mathlib.GroupTheory.Coxeter.Length

/-!
# Fixed-word reduced-subword interface

This file contains the elementary Coxeter-word definitions used by the
representation-directed proof.  They were formerly bundled with an optional
Dynkin/Oppermann--Reiten--Thomas parametrization, although they require no
Dynkin or root-system input.
-/

noncomputable section

namespace OpConjecture.RepresentationDirected.FixedWord

universe uB uW

/-- The subword of `word` selected by a finite set of positions, read in
increasing position order. -/
def subwordAt
    {B : Type uB}
    (word : List B)
    (positions : Finset (Fin word.length)) :
    List B :=
  (positions.sort (· ≤ ·)).map word.get

@[simp]
theorem length_subwordAt
    {B : Type uB}
    (word : List B)
    (positions : Finset (Fin word.length)) :
    (subwordAt word positions).length = positions.card := by
  simp [subwordAt, Finset.length_sort]

/-- `positions` selects a reduced expression for `w` from `ambient`. -/
def IsReducedSubwordFor
    {B : Type uB} {W : Type uW}
    [Group W] {M : CoxeterMatrix B}
    (cs : CoxeterSystem M W)
    (ambient : List B) (w : W)
    (positions : Finset (Fin ambient.length)) :
    Prop :=
  cs.IsReduced (subwordAt ambient positions) ∧
    cs.wordProd (subwordAt ambient positions) = w

/-- Lexicographically leftmost means that no other reduced position set for
`w` has a lexicographically smaller increasing list of positions. -/
def IsLeftmostReducedSubwordFor
    {B : Type uB} {W : Type uW}
    [Group W] {M : CoxeterMatrix B}
    (cs : CoxeterSystem M W)
    (ambient : List B) (w : W)
    (positions : Finset (Fin ambient.length)) :
    Prop :=
  IsReducedSubwordFor cs ambient w positions ∧
    ∀ other : Finset (Fin ambient.length),
      IsReducedSubwordFor cs ambient w other →
        ¬ List.Lex (· < ·)
          (other.sort (· ≤ ·))
          (positions.sort (· ≤ ·))

end OpConjecture.RepresentationDirected.FixedWord
