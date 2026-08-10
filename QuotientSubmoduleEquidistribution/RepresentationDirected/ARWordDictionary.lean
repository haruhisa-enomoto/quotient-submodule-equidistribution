import QuotientSubmoduleEquidistribution.RepresentationDirected.OrderedARWord
import QuotientSubmoduleEquidistribution.RepresentationDirected.IrreducibleMultiplicityOne
import QuotientSubmoduleEquidistribution.RepresentationTheory.ProjectiveBoundaryAlmostSplit

/-!
# The Auslander--Reiten word dictionary

This file connects the middle-position rule in the ordered AR word to
minimal right almost-split middle terms.  The dictionary is uniform at
projective and nonprojective endpoints: at a projective endpoint the middle
term is literally the module radical.

The support results are field-free.  The final algebraically closed,
finite-dimensional specialization applies the representation-directed
irreducible-space theorem to prove that the decomposition labels are
injective, so the dictionary also retains coordinate multiplicity.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.RepresentationDirected.DirectedAROrbit.OrderedARWord

universe uR uIota

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {Iota : Type uIota} [Fintype Iota]
  (sigma : IndecomposableSkeleton.{uR, uIota, uR} R Iota)

omit [Fintype Iota] in
/-- A chosen minimal right almost-split decomposition at every label.  At a
projective label this is the radical inclusion; otherwise it is the chosen
AR sequence ending at that label. -/
def chosenRightARAt (D : ARData sigma) (x : Iota) :
    sigma.MinimalRightAlmostSplitDecomposition x := by
  classical
  by_cases hx : Projective (sigma.obj x)
  · exact sigma.projectiveBoundaryMinimalRightAlmostSplitDecomposition x hx
  · exact D.chosenRightAR sigma ⟨x, hx⟩

omit [Fintype Iota] in
/-- The support of the unified right almost-split middle term is exactly the
incoming irreducible support. -/
theorem mem_chosenRightARAt_iff_irreducible
    (D : ARData sigma) (x y : Iota) :
    (∃ t : (chosenRightARAt sigma D x).index,
      (chosenRightARAt sigma D x).label t = y) ↔
      HasIrreducibleMorphism (sigma.obj y) (sigma.obj x) :=
  (chosenRightARAt sigma D x).summandIrreducibleCorrespondence y

omit [Fintype Iota] in
/-- Set-valued form of the support correspondence. -/
theorem chosenRightARAt_support_eq_incomingIrreducible
    (D : ARData sigma) (x : Iota) :
    Set.range (chosenRightARAt sigma D x).label =
      {y : Iota | HasIrreducibleMorphism (sigma.obj y) (sigma.obj x)} := by
  ext y
  change (∃ t : (chosenRightARAt sigma D x).index,
    (chosenRightARAt sigma D x).label t = y) ↔ _
  exact mem_chosenRightARAt_iff_irreducible sigma D x y

/-- Over an algebraically closed field, the unified right almost-split
middle decomposition has no repeated label.  This includes both ordinary AR
sequences and projective radical decompositions. -/
theorem chosenRightARAt_label_injective
    (K : Type uR) [Field K] [IsAlgClosed K]
    [Algebra K R] [FiniteDimensional K R]
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (x : Iota) :
    Function.Injective (chosenRightARAt sigma D x).label :=
  H.rightARLabel_injective (K := K) (R := R) sigma
    (chosenRightARAt sigma D x)

/-- A position belongs to the middle window at `x` exactly when its module
label occurs in the chosen right almost-split middle ending at `x`. -/
theorem isMiddle_iff_mem_chosenRightARAt
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma)
    (y x : Fin (word sigma H D).length) :
    ARWord.IsMiddle (orbitGraph sigma H D) (word sigma H D) y x ↔
      ∃ t : (chosenRightARAt sigma D
          (positionEquiv sigma H D x)).index,
        (chosenRightARAt sigma D
          (positionEquiv sigma H D x)).label t =
            positionEquiv sigma H D y :=
  (isMiddle_iff_hasIrreducibleMorphism sigma H D y x).trans
    (mem_chosenRightARAt_iff_irreducible sigma D
      (positionEquiv sigma H D x) (positionEquiv sigma H D y)).symm

/-- Multiplicity-preserving form of the ordered-word dictionary: the actual
coordinates of the chosen right almost-split middle term are in bijection
with the middle positions of the word. -/
def middleIndexEquiv
    (K : Type uR) [Field K] [IsAlgClosed K]
    [Algebra K R] [FiniteDimensional K R]
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma)
    (x : Fin (word sigma H D).length) :
    (chosenRightARAt sigma D
        (positionEquiv sigma H D x)).index ≃
      {y : Fin (word sigma H D).length //
        ARWord.IsMiddle (orbitGraph sigma H D) (word sigma H D) y x} := by
  classical
  let A := chosenRightARAt sigma D (positionEquiv sigma H D x)
  let f : A.index →
      {y : Fin (word sigma H D).length //
        ARWord.IsMiddle (orbitGraph sigma H D) (word sigma H D) y x} :=
    fun t ↦ ⟨(positionEquiv sigma H D).symm (A.label t),
      (isMiddle_iff_mem_chosenRightARAt sigma H D _ x).2
        ⟨t, (positionEquiv_symm_apply_apply sigma H D (A.label t)).symm⟩⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro t u htu
    apply chosenRightARAt_label_injective sigma K H D
      (positionEquiv sigma H D x)
    exact (positionEquiv sigma H D).symm.injective
      (congrArg Subtype.val htu)
  · rintro ⟨y, hy⟩
    obtain ⟨t, ht⟩ :=
      (isMiddle_iff_mem_chosenRightARAt sigma H D y x).1 hy
    refine ⟨t, Subtype.ext ?_⟩
    change (positionEquiv sigma H D).symm (A.label t) = y
    rw [ht, positionEquiv_apply_symm_apply]

/-- Coordinate-free version: the module at a middle position is precisely
an indecomposable retract of the chosen right almost-split middle term. -/
theorem isMiddle_iff_retract_chosenRightARAtMiddle
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma)
    (y x : Fin (word sigma H D).length) :
    ARWord.IsMiddle (orbitGraph sigma H D) (word sigma H D) y x ↔
      Nonempty (Retract (sigma.obj (positionEquiv sigma H D y))
        (chosenRightARAt sigma D
          (positionEquiv sigma H D x)).middle) :=
  (isMiddle_iff_hasIrreducibleMorphism sigma H D y x).trans
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.MinimalRightAlmostSplitDecomposition.indecomposableRetract_middle_iff_irreducible
        (chosenRightARAt sigma D (positionEquiv sigma H D x))
        (positionEquiv sigma H D y)).symm

/-- The modules represented by middle positions are exactly the distinct
indecomposable types in the chosen right almost-split middle.  This set
identity deliberately forgets coordinate multiplicity. -/
theorem image_middlePositions_eq_chosenRightARAt_support
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (x : Fin (word sigma H D).length) :
    positionEquiv sigma H D ''
        {y : Fin (word sigma H D).length |
          ARWord.IsMiddle (orbitGraph sigma H D) (word sigma H D) y x} =
      Set.range (chosenRightARAt sigma D
        (positionEquiv sigma H D x)).label := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.MinimalRightAlmostSplitDecomposition.summandIrreducibleCorrespondence
        (chosenRightARAt sigma D (positionEquiv sigma H D x))
        (positionEquiv sigma H D y)).2
      ((isMiddle_iff_hasIrreducibleMorphism sigma H D y x).1 hy)
  · intro hz
    let y : Fin (word sigma H D).length :=
      (positionEquiv sigma H D).symm z
    have hirr : HasIrreducibleMorphism
        (sigma.obj (positionEquiv sigma H D y))
        (sigma.obj (positionEquiv sigma H D x)) := by
      simpa only [y, positionEquiv_symm_apply_apply] using
        (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.MinimalRightAlmostSplitDecomposition.summandIrreducibleCorrespondence
            (chosenRightARAt sigma D (positionEquiv sigma H D x)) z).1 hz
    exact ⟨y, (isMiddle_iff_hasIrreducibleMorphism sigma H D y x).2 hirr,
      positionEquiv_symm_apply_apply sigma H D z⟩

/-- Projective-boundary specialization: middle positions at a projective
module are exactly the indecomposable retracts of its module radical. -/
theorem isMiddle_iff_retract_projectiveBoundaryRadical
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma)
    (y x : Fin (word sigma H D).length)
    (hx : Projective (sigma.obj (positionEquiv sigma H D x))) :
    ARWord.IsMiddle (orbitGraph sigma H D) (word sigma H D) y x ↔
      Nonempty (Retract (sigma.obj (positionEquiv sigma H D y))
        (sigma.projectiveBoundaryRadical
          (positionEquiv sigma H D x))) :=
  (isMiddle_iff_hasIrreducibleMorphism sigma H D y x).trans
    (sigma.indecomposableRetract_projectiveBoundaryRadical_iff_irreducible
      (positionEquiv sigma H D x) hx
      (positionEquiv sigma H D y)).symm

/-! ## Explicit directed-order dictionary -/

/-- A position in an explicit-order word is a middle position exactly when
its label occurs in the chosen right almost-split middle term. -/
theorem isMiddle_iff_mem_chosenRightARAtFor
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (E : DirectedOrderChoice sigma)
    (y x : Fin (wordFor sigma H D E).length) :
    ARWord.IsMiddle (orbitGraph sigma H D) (wordFor sigma H D E) y x ↔
      ∃ t : (chosenRightARAt sigma D
          (positionEquivFor sigma H D E x)).index,
        (chosenRightARAt sigma D
          (positionEquivFor sigma H D E x)).label t =
            positionEquivFor sigma H D E y :=
  (isMiddle_iff_hasIrreducibleMorphismFor sigma H D E y x).trans
    (mem_chosenRightARAt_iff_irreducible sigma D
      (positionEquivFor sigma H D E x)
      (positionEquivFor sigma H D E y)).symm

/-- Multiplicity-preserving dictionary for an explicit directed order. -/
def middleIndexEquivFor
    (K : Type uR) [Field K] [IsAlgClosed K]
    [Algebra K R] [FiniteDimensional K R]
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (E : DirectedOrderChoice sigma)
    (x : Fin (wordFor sigma H D E).length) :
    (chosenRightARAt sigma D
        (positionEquivFor sigma H D E x)).index ≃
      {y : Fin (wordFor sigma H D E).length //
        ARWord.IsMiddle (orbitGraph sigma H D)
          (wordFor sigma H D E) y x} := by
  classical
  let A := chosenRightARAt sigma D (positionEquivFor sigma H D E x)
  let f : A.index →
      {y : Fin (wordFor sigma H D E).length //
        ARWord.IsMiddle (orbitGraph sigma H D)
          (wordFor sigma H D E) y x} :=
    fun t ↦ ⟨(positionEquivFor sigma H D E).symm (A.label t),
      (isMiddle_iff_mem_chosenRightARAtFor sigma H D E _ x).2
        ⟨t, (positionEquivFor_symm_apply_apply
          sigma H D E (A.label t)).symm⟩⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro t s hts
    apply chosenRightARAt_label_injective sigma K H D
      (positionEquivFor sigma H D E x)
    exact (positionEquivFor sigma H D E).symm.injective
      (congrArg Subtype.val hts)
  · rintro ⟨y, hy⟩
    obtain ⟨t, ht⟩ :=
      (isMiddle_iff_mem_chosenRightARAtFor sigma H D E y x).1 hy
    refine ⟨t, Subtype.ext ?_⟩
    change (positionEquivFor sigma H D E).symm (A.label t) = y
    rw [ht, positionEquivFor_apply_symm_apply]

end QuotientSubmoduleEquidistribution.RepresentationDirected.DirectedAROrbit.OrderedARWord
