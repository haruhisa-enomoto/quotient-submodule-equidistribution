import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.GroupTheory.Coxeter.Inversion

/-!
# The simply-laced Coxeter group of a simple graph

This file attaches the paper's Coxeter matrix, presented group, and canonical
Coxeter system to an arbitrary simple graph.  It does not assume that the
graph or Coxeter group is of finite type.
-/

noncomputable section

namespace QuotientSubmoduleEquidistribution.RepresentationDirected.SimpleGraphCoxeter

universe u

variable {L : Type u}

/-- The simply-laced Coxeter matrix attached to a simple graph. -/
def matrix (G : SimpleGraph L) : CoxeterMatrix L := by
  classical
  exact
    { M := fun i j => if i = j then 1 else if G.Adj i j then 3 else 2
      isSymm := by
        unfold Matrix.IsSymm
        ext i j
        simp only [Matrix.transpose_apply]
        by_cases hij : i = j
        · subst j
          simp
        · have hji : j ≠ i := Ne.symm hij
          simp only [hij, hji, if_false]
          rw [G.adj_comm]
      diagonal := by simp
      off_diagonal := by
        intro i j hij
        by_cases hadj : G.Adj i j <;> simp [hij, hadj] }

@[simp]
theorem matrix_apply_self (G : SimpleGraph L) (i : L) :
    matrix G i i = 1 := by
  simp [matrix]

@[simp]
theorem matrix_apply_of_adj (G : SimpleGraph L) {i j : L}
    (hij : G.Adj i j) :
    matrix G i j = 3 := by
  have hne : i ≠ j := hij.ne
  simp [matrix, hne, hij]

@[simp]
theorem matrix_apply_of_ne_of_not_adj (G : SimpleGraph L) {i j : L}
    (hne : i ≠ j) (hij : ¬ G.Adj i j) :
    matrix G i j = 2 := by
  simp [matrix, hne, hij]

/-- The presented simply-laced Coxeter group attached to `G`. -/
abbrev Group (G : SimpleGraph L) := (matrix G).Group

/-- The canonical Coxeter system on the presented group. -/
abbrev system (G : SimpleGraph L) : CoxeterSystem (matrix G) (Group G) :=
  (matrix G).toCoxeterSystem

/-- The group element represented by a graph-label word. -/
def wordProd (G : SimpleGraph L) (Q : List L) : Group G :=
  (system G).wordProd Q

/-- Reducedness of a graph-label word in the attached Coxeter group. -/
def IsReduced (G : SimpleGraph L) (Q : List L) : Prop :=
  (system G).IsReduced Q

end QuotientSubmoduleEquidistribution.RepresentationDirected.SimpleGraphCoxeter
