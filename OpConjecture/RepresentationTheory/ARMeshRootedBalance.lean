import OpConjecture.Combinatorics.RootedDigraphRotation
import OpConjecture.RepresentationTheory.FactorLadderRooted
import OpConjecture.RepresentationTheory.FiniteTypeARTranslation

/-!
# Rooted balance from AR mesh rotation

The AR translation equivalence is extended arbitrarily across the
projective/injective boundaries.  On nonprojective vertices the extension
is the literal AR translate.  Applying mesh incidence once identifies the
forced predecessor regions; applying it twice gives the internal graph
anti-isomorphism required by grouped rooted inclusion--exclusion.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace OpConjecture.IndecomposableSkeleton

universe u v

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} [Fintype ι] [DecidableEq ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)

namespace ARMeshRotationData

variable (M : σ.ARMeshRotationData)

/-- Extend AR translation to an arbitrary permutation of all labels by
matching the projective and injective boundary complements. -/
def vertexPerm : Equiv.Perm ι := by
  classical
  exact M.tau.extendSubtype

omit [DecidableEq ι] in
/-- The extended permutation agrees with AR translation away from the
projective boundary. -/
theorem vertexPerm_apply_of_nonprojective
    (x : ι) (hx : ¬ Projective (σ.obj x)) :
    vertexPerm σ M x = (M.tau ⟨x, hx⟩).1 := by
  classical
  exact Equiv.extendSubtype_apply_of_mem M.tau x hx

omit [DecidableEq ι] in
/-- The extended permutation identifies the complements of the projective
and injective boundaries. -/
theorem not_mem_projective_iff_vertexPerm_not_mem_injective (x : ι) :
    x ∉ σ.projectiveLabelFinset ↔
      vertexPerm σ M x ∉ σ.injectiveLabelFinset := by
  classical
  simp only [mem_projectiveLabelFinset, mem_injectiveLabelFinset]
  constructor
  · intro hx
    have hmem : ¬ Injective (σ.obj (vertexPerm σ M x)) := by
      simpa [vertexPerm] using
        (Equiv.extendSubtype_mem M.tau x hx)
    exact hmem
  · intro hx
    by_contra hproj
    have hnotmem : ¬¬ Injective (σ.obj (vertexPerm σ M x)) := by
      simpa [vertexPerm] using
        (Equiv.extendSubtype_not_mem M.tau x (by simpa using hproj))
    exact hnotmem hx

omit [DecidableEq ι] in
/-- Two uses of mesh incidence show that AR translation preserves internal
irreducible adjacency on nonprojective vertices. -/
theorem irreducibleEdge_iff_vertexPerm
    {x y : ι}
    (hx : ¬ Projective (σ.obj x))
    (hy : ¬ Projective (σ.obj y)) :
    σ.irreducibleEdge x y ↔
      σ.irreducibleEdge (vertexPerm σ M x) (vertexPerm σ M y) := by
  rw [vertexPerm_apply_of_nonprojective σ M x hx,
    vertexPerm_apply_of_nonprojective σ M y hy]
  exact (M.incidence ⟨y, hy⟩ x).trans
    (M.incidence ⟨x, hx⟩ (M.tau ⟨y, hy⟩).1)

omit [DecidableEq ι] in
/-- One use of mesh incidence rotates an incoming arrow at a support vertex
to an outgoing arrow from its AR translate. -/
theorem irreducibleEdge_iff_vertexPerm_target
    {x y : ι} (hy : ¬ Projective (σ.obj y)) :
    σ.irreducibleEdge x y ↔
      σ.irreducibleEdge (vertexPerm σ M y) x := by
  rw [vertexPerm_apply_of_nonprojective σ M y hy]
  exact M.incidence ⟨y, hy⟩ x

/-- AR mesh rotation realizes the graph-theoretic grouped-rotation
interface.  The target relation is the reversed irreducible AR relation. -/
def groupedRotationData :
    OpConjecture.RootedDigraph.GroupedRotationData
      σ.irreducibleEdge (fun x y ↦ σ.irreducibleEdge y x)
        σ.projectiveLabelFinset σ.injectiveLabelFinset where
  perm := vertexPerm σ M
  nonboundary_iff := not_mem_projective_iff_vertexPerm_not_mem_injective σ M
  edge_iff := by
    intro x y hx hy
    have hx' : ¬ Projective (σ.obj x) := by simpa using hx
    have hy' : ¬ Projective (σ.obj y) := by simpa using hy
    simpa using irreducibleEdge_iff_vertexPerm σ M
      hx' hy'
  incoming_iff := by
    intro x y hy
    have hy' : ¬ Projective (σ.obj y) := by simpa using hy
    simpa using irreducibleEdge_iff_vertexPerm_target σ M
      hy'

/-- The grouped matching in the rooted-balance lemma, constructed solely
from AR mesh rotation. -/
def groupedTopPartMatching :
    OpConjecture.RootedDigraph.GroupedTopPartMatching
      σ.irreducibleEdge (fun x y ↦ σ.irreducibleEdge y x)
        σ.projectiveLabelFinset σ.injectiveLabelFinset :=
  (groupedRotationData σ M).groupedTopPartMatching

include M in
/-- Rooted balance: projectively rooted and injectively corooted deletion
sets have the same cardinality in every size. -/
theorem projectivelyRootedSets_card_eq_injectivelyCorootedSets_card
    (j : ℕ) :
    (OpConjecture.RootedDigraph.projectivelyRootedSets
      σ.irreducibleEdge σ.projectiveLabelFinset j).card =
    (OpConjecture.RootedDigraph.injectivelyCorootedSets
      σ.irreducibleEdge σ.injectiveLabelFinset j).card :=
  OpConjecture.RootedDigraph.projectivelyRootedSets_card_eq_injectivelyCorootedSets_card_of_groupedMatching
    (groupedTopPartMatching σ M) j

end ARMeshRotationData

section FiniteDimensional

variable {k : Type u} [Field k] [Algebra k R]
  [FiniteDimensional k R] [IsNoetherianRing Rᵐᵒᵖ]

include k in
/-- The actual finite-dimensional AR data prove the manuscript's rooted
balance lemma without an additional graph hypothesis. -/
theorem finiteDimensional_projectivelyRootedSets_card_eq_injectivelyCorootedSets_card
    (j : ℕ) :
    (OpConjecture.RootedDigraph.projectivelyRootedSets
      σ.irreducibleEdge σ.projectiveLabelFinset j).card =
    (OpConjecture.RootedDigraph.injectivelyCorootedSets
      σ.irreducibleEdge σ.injectiveLabelFinset j).card :=
  (σ.finiteDimensionalARMeshRotationData (K := k)).projectivelyRootedSets_card_eq_injectivelyCorootedSets_card
    σ j

end FiniteDimensional

end OpConjecture.IndecomposableSkeleton
