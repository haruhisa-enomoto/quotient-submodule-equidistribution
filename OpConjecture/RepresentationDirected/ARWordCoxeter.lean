import OpConjecture.RepresentationDirected.OrderedARWord
import OpConjecture.RepresentationDirected.SimpleGraphCoxeter

/-!
# Coxeter data of the ordered Auslander--Reiten word

This file instantiates the simply-laced graph Coxeter construction on the
translation-orbit graph of a finite representation-directed skeleton.  The
resulting group is allowed to be infinite.
-/

noncomputable section

namespace OpConjecture.RepresentationDirected.DirectedAROrbit.OrderedARWord

universe uR uIota

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {Iota : Type uIota} [Fintype Iota]
  (sigma : IndecomposableSkeleton.{uR, uIota, uR} R Iota)

/-- The paper's simply-laced Coxeter matrix on AR translation orbits. -/
def coxeterMatrix
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) : CoxeterMatrix (ProjectiveLabel sigma) :=
  SimpleGraphCoxeter.matrix (orbitGraph sigma H D)

/-- The paper's Coxeter group `W(Delta_A)`. -/
abbrev CoxeterGroup
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) :=
  SimpleGraphCoxeter.Group (orbitGraph sigma H D)

/-- Its canonical Coxeter system. -/
abbrev coxeterSystem
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) :
    CoxeterSystem (coxeterMatrix sigma H D) (CoxeterGroup sigma H D) :=
  SimpleGraphCoxeter.system (orbitGraph sigma H D)

/-- The Coxeter-group element represented by the ordered AR word. -/
def coxeterWordElement
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) : CoxeterGroup sigma H D :=
  (coxeterSystem sigma H D).wordProd (word sigma H D)

/-- The exact reducedness proposition asserted for the ordered AR word. -/
def IsReducedCoxeterWord
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) : Prop :=
  (coxeterSystem sigma H D).IsReduced (word sigma H D)

end OpConjecture.RepresentationDirected.DirectedAROrbit.OrderedARWord
