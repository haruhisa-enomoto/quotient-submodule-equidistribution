import OpConjecture.RepresentationDirected.FixedWordSortingExchange
import OpConjecture.RepresentationDirected.ProfileInterface

/-!
# Fixed-word sorted supports and their length profile

This file turns the unconditional local recognition theorem into the finite
bijection and generating-function statement immediately upstream of the
Bruhat/profile part of the representation-directed proof.
-/

set_option autoImplicit false

noncomputable section

namespace OpConjecture.RepresentationDirected.FixedWordProfile

open Polynomial
open OpConjecture.RepresentationDirected.FixedWord
open FixedWordSubwords SortingExchange

universe uB uW uL

variable {B : Type uB} {W : Type uW}
variable [Group W] {M : CoxeterMatrix B}
variable (cs : CoxeterSystem M W)

/-- Lexicographically leftmost reduced position sets are unique. -/
theorem isLeftmostReducedSubwordFor_unique
    (ambient : List B) (w : W)
    {D E : Finset (Fin ambient.length)}
    (hD : IsLeftmostReducedSubwordFor cs ambient w D)
    (hE : IsLeftmostReducedSubwordFor cs ambient w E) :
    D = E := by
  by_contra hDE
  have hsortNe : D.sort (· ≤ ·) ≠ E.sort (· ≤ ·) := by
    intro hsort
    apply hDE
    ext x
    rw [← Finset.mem_sort (r := (· ≤ ·)), hsort,
      Finset.mem_sort]
  rcases lt_or_gt_of_ne hsortNe with hlt | hgt
  · exact hE.2 D hD.1
      ((List.lt_iff_lex_lt _ _).mp hlt)
  · exact hD.2 E hE.1
      ((List.lt_iff_lex_lt _ _).mp hgt)

/-- The chosen lex-first position map is injective. -/
theorem lexFirstPositions_injective
    (ambient : List B) :
    Function.Injective (lexFirstPositions cs ambient) := by
  intro u v huv
  apply Subtype.ext
  have hu := (lexFirstPositions_spec cs ambient u).1.2
  have hv := (lexFirstPositions_spec cs ambient v).1.2
  calc
    u.1 = cs.wordProd
        (subwordAt ambient (lexFirstPositions cs ambient u)) := hu.symm
    _ = cs.wordProd
        (subwordAt ambient (lexFirstPositions cs ambient v)) := by rw [huv]
    _ = v.1 := hv

section SimpleGraph

open SimpleGraphCoxeter

variable {L : Type uL} [Fintype L]

/-- Position sets satisfying all local `D[a]` reducedness tests. -/
def LocallyReducedPositions
    (G : SimpleGraph L) (ambient : List L) :=
  {D : Finset (Fin ambient.length) //
    AreAllLocalSubwordsReduced (system G) ambient D}

/-- The lex-first position set of a fixed-word element is locally reduced. -/
def lexFirstLocalPositions
    (G : SimpleGraph L) (ambient : List L) :
    FixedWordElement (system G) ambient →
      LocallyReducedPositions G ambient :=
  fun u ↦ ⟨lexFirstPositions (system G) ambient u,
    ((leftmostReducedSubwordFor_iff_product_eq_and_allLocal_simpleGraph
      G ambient u.1 (lexFirstPositions (system G) ambient u)).mp
        (lexFirstPositions_spec (system G) ambient u)).2⟩

theorem lexFirstLocalPositions_injective
    (G : SimpleGraph L) (ambient : List L) :
    Function.Injective (lexFirstLocalPositions G ambient) := by
  intro u v huv
  apply lexFirstPositions_injective (system G) ambient
  exact congrArg Subtype.val huv

theorem lexFirstLocalPositions_surjective
    (G : SimpleGraph L) (ambient : List L) :
    Function.Surjective (lexFirstLocalPositions G ambient) := by
  rintro ⟨D, hDlocal⟩
  let w : Group G := (system G).wordProd (subwordAt ambient D)
  have hleft : IsLeftmostReducedSubwordFor (system G) ambient w D :=
    (leftmostReducedSubwordFor_iff_product_eq_and_allLocal_simpleGraph
      G ambient w D).2 ⟨rfl, hDlocal⟩
  let u : FixedWordElement (system G) ambient :=
    ⟨w, ⟨D, hleft.1⟩⟩
  refine ⟨u, Subtype.ext ?_⟩
  exact isLeftmostReducedSubwordFor_unique (system G) ambient w
    (lexFirstPositions_spec (system G) ambient u) hleft

/-- Fixed-word elements are in bijection with locally reduced position
sets, with no assumption that the ambient word itself is reduced. -/
def fixedWordElementEquivLocallyReducedPositions
    (G : SimpleGraph L) (ambient : List L) :
    FixedWordElement (system G) ambient ≃
      LocallyReducedPositions G ambient :=
  Equiv.ofBijective (lexFirstLocalPositions G ambient)
    ⟨lexFirstLocalPositions_injective G ambient,
      lexFirstLocalPositions_surjective G ambient⟩

/-- A lex-first support has cardinality equal to the Coxeter length of the
element it represents. -/
theorem card_lexFirstLocalPositions
    (G : SimpleGraph L) (ambient : List L)
    (u : FixedWordElement (system G) ambient) :
    (lexFirstLocalPositions G ambient u).1.card =
      (system G).length u.1 := by
  let D := lexFirstPositions (system G) ambient u
  have hspec := lexFirstPositions_spec (system G) ambient u
  calc
    D.card = (subwordAt ambient D).length :=
      (length_subwordAt ambient D).symm
    _ = (system G).length
        ((system G).wordProd (subwordAt ambient D)) := hspec.1.1.eq.symm
    _ = (system G).length u.1 := by rw [hspec.1.2]

/-- Transport the canonical finite structure across the sorted-support
bijection. -/
noncomputable instance locallyReducedPositionsFintype
    (G : SimpleGraph L) (ambient : List L) :
    Fintype (LocallyReducedPositions G ambient) :=
  Fintype.ofEquiv (FixedWordElement (system G) ambient)
    (fixedWordElementEquivLocallyReducedPositions G ambient)

/-- The locally reduced support enumerator is the reverse Coxeter-length
enumerator of the elements admitting a reduced subword in `ambient`. -/
theorem locallyReducedPositions_generatingFunction
    (G : SimpleGraph L) (ambient : List L) :
    (∑ D : LocallyReducedPositions G ambient,
        X ^ (ambient.length - D.1.card) : ℕ[X]) =
      ∑ u : FixedWordElement (system G) ambient,
        X ^ (ambient.length - (system G).length u.1) := by
  let e := fixedWordElementEquivLocallyReducedPositions G ambient
  calc
    (∑ D : LocallyReducedPositions G ambient,
        X ^ (ambient.length - D.1.card) : ℕ[X]) =
        ∑ u : FixedWordElement (system G) ambient,
          X ^ (ambient.length - (e u).1.card) := by
      exact (e.sum_comp
        (fun D : LocallyReducedPositions G ambient ↦
          (X ^ (ambient.length - D.1.card) : ℕ[X]))).symm
    _ = ∑ u : FixedWordElement (system G) ambient,
        X ^ (ambient.length - (system G).length u.1) := by
      apply Finset.sum_congr rfl
      intro u _
      rw [show e u = lexFirstLocalPositions G ambient u by rfl,
        card_lexFirstLocalPositions]

end SimpleGraph


end OpConjecture.RepresentationDirected.FixedWordProfile
