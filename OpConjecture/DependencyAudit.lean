import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.GroupTheory.Coxeter.Inversion
import Mathlib.Order.Closure
import OpConjecture.Foundation.RepresentationTheory.Quiver.PathAlgebra
import OpConjecture.Foundation.RepresentationTheory.Quiver.Representation.Basic
import OpConjecture.Foundation.RingTheory.KrullSchmidt.Indecomposable

/-!
# Dependency audit

This file is a compilation check for the foundational APIs expected by the
formalization. It should remain mathematically trivial.
-/

namespace OpConjecture.DependencyAudit

example {α : Type*} [Preorder α] (c : ClosureOperator α) : Monotone c :=
  c.monotone

#check CategoryTheory.Abelian
#check CoxeterSystem
#check OpConjecture.Foundation.QuiverRep
#check OpConjecture.Foundation.IsIndecomposableModule
#check OpConjecture.Foundation.pathAlgebra

end OpConjecture.DependencyAudit
