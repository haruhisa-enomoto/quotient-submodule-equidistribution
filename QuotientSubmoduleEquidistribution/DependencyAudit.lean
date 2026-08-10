import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.GroupTheory.Coxeter.Inversion
import Mathlib.Order.Closure
import QuotientSubmoduleEquidistribution.Foundation.RepresentationTheory.Quiver.PathAlgebra
import QuotientSubmoduleEquidistribution.Foundation.RepresentationTheory.Quiver.Representation.Basic
import QuotientSubmoduleEquidistribution.Foundation.RingTheory.KrullSchmidt.Indecomposable

/-!
# Dependency audit

This file is a compilation check for the foundational APIs expected by the
formalization. It should remain mathematically trivial.
-/

namespace QuotientSubmoduleEquidistribution.DependencyAudit

example {α : Type*} [Preorder α] (c : ClosureOperator α) : Monotone c :=
  c.monotone

#check CategoryTheory.Abelian
#check CoxeterSystem
#check QuotientSubmoduleEquidistribution.Foundation.QuiverRep
#check QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule
#check QuotientSubmoduleEquidistribution.Foundation.pathAlgebra

end QuotientSubmoduleEquidistribution.DependencyAudit
