import QuotientSubmoduleEquidistribution.RadicalSquareZero.SeparatedLabelAssembly
import QuotientSubmoduleEquidistribution.RadicalSquareZero.SeparatedModelAssembly
import QuotientSubmoduleEquidistribution.RadicalSquareZero.OriginalLabelAssembly

/-!
# Canonical separated assembly

The classification of triangular indecomposables by the three canonical
candidate families gives a literal relabeling of an arbitrary target
skeleton.  This file supplies all objectwise alignment data required by the
separated quotient model and derives the Boolean-factor identity without an
extra classification hypothesis.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.RadicalSquareZero

open SeparatedTriangularAlgebra
open TrivSqZeroExtSeparatedCorrespondence
open TrivSqZeroExtSeparatedData
open TrivSqZeroExtSeparatedSimple

universe u v w x y z

variable {S : Type u} {J : Type v}
variable [CommRing S] [AddCommGroup J]
variable [Module S J] [Module Sᵐᵒᵖ J]
variable [SMulCommClass S Sᵐᵒᵖ J]
variable [IsSemisimpleRing S] [Module.Finite S J]
variable [IsNoetherianRing (TrivSqZeroExt S J)]
variable [IsNoetherianRing (Algebra S J)]
variable {Nonsimple : Type x} {Vertex : Type y} {kappa : Type z}
variable
  {sigma : IndecomposableSkeleton.{max u v, max x y, w}
    (TrivSqZeroExt S J) (Nonsimple ⊕ Vertex)}
variable
  (tau : IndecomposableSkeleton.{max u v, z, w}
    (Algebra S J) kappa)

/-- Relabel an arbitrary complete target skeleton by the canonical
nonsimple, covered-simple, and free-simple families. -/
abbrev canonicalSeparatedSkeleton
    (L : OriginalNonsimpleLabelData Nonsimple Vertex sigma) :
    IndecomposableSkeleton.{max u v, max x y, w}
      (Algebra S J) (Nonsimple ⊕ (Vertex ⊕ Vertex)) :=
  tau.relabel (separatedCandidateEquiv tau L)

/-- Each canonical candidate is isomorphic to the object carrying its
literal label in the relabeled target skeleton. -/
def canonicalSeparatedCandidateIso
    (L : OriginalNonsimpleLabelData Nonsimple Vertex sigma)
    (i : Nonsimple ⊕ (Vertex ⊕ Vertex)) :
    separatedCandidateFG (sigma := sigma) i ≅
      (canonicalSeparatedSkeleton tau L).obj i := by
  simpa [canonicalSeparatedSkeleton] using separatedCandidateIso tau L i

/-- The two vertex copies in the canonical relabeling are simple. -/
theorem canonicalSeparatedSimpleLabelData
    [Fintype Nonsimple] [Fintype Vertex]
    (L : OriginalNonsimpleLabelData Nonsimple Vertex sigma) :
    SeparatedSimpleLabelData (canonicalSeparatedSkeleton tau L) where
  covered_simple a := by
    apply (Simple.iff_of_iso
      (canonicalSeparatedCandidateIso tau L (Sum.inr (Sum.inl a)))).1
    exact (separatedCandidateFG_simple_iff L _).2
      ⟨a, Or.inl rfl⟩
  free_simple a := by
    apply (Simple.iff_of_iso
      (canonicalSeparatedCandidateIso tau L (Sum.inr (Sum.inr a)))).1
    exact (separatedCandidateFG_simple_iff L _).2
      ⟨a, Or.inr rfl⟩

/-- The canonical relabeling realizes the separated data of every original
nonsimple and the free copy of every original simple. -/
def canonicalSeparatedNonsimpleFreeData
    [Fintype Nonsimple] [Fintype Vertex]
    (L : OriginalNonsimpleLabelData Nonsimple Vertex sigma) :
    SeparatedNonsimpleFreeData (canonicalSeparatedSkeleton tau L) where
  nonsimpleData n :=
    moduleSeparatedData (S := S) (J := J)
      (sigma.obj (Sum.inl n)).obj
  nonsimple_generated n := moduleSeparatedData_isGenerated _
  nonsimple_iso n := by
    let V := forget₂ (FGModuleCat.{w} (Algebra S J))
      (ModuleCat.{w} (Algebra S J))
    exact V.mapIso
      (canonicalSeparatedCandidateIso tau L (Sum.inl n))
  freeData a :=
    freeData (S := S) (J := J) (sigma.obj (Sum.inr a)).obj
  free_top_subsingleton a := inferInstance
  free_iso a := by
    let V := forget₂ (FGModuleCat.{w} (Algebra S J))
      (ModuleCat.{w} (Algebra S J))
    exact V.mapIso
      (canonicalSeparatedCandidateIso tau L (Sum.inr (Sum.inr a)))

/-- The nonsimple and covered-simple pieces of the canonical relabeling are
the separated realizations extracted from the original skeleton. -/
def canonicalSeparatedCoreAlignment
    [Fintype Nonsimple] [DecidableEq Nonsimple]
    [Fintype Vertex] [DecidableEq Vertex]
    (L : OriginalNonsimpleLabelData Nonsimple Vertex sigma) :
    OriginalNonsimpleLabelData.SeparatedCoreAlignment sigma
      (canonicalSeparatedSkeleton tau L)
      (canonicalSeparatedNonsimpleFreeData tau L) where
  nonsimple_data_eq _ := rfl
  covered_iso a := by
    let V := forget₂ (FGModuleCat.{w} (Algebra S J))
      (ModuleCat.{w} (Algebra S J))
    exact V.mapIso
      (canonicalSeparatedCandidateIso tau L (Sum.inr (Sum.inl a)))

/-- The separated quotient-closure polynomial has the paper's Boolean
factor for any complete triangular target skeleton. -/
theorem canonicalSeparatedLevelPolynomial_eq_original_mul
    [Fintype Nonsimple] [DecidableEq Nonsimple]
    [Fintype Vertex] [DecidableEq Vertex]
    (L : OriginalNonsimpleLabelData Nonsimple Vertex sigma) :
    (canonicalSeparatedSkeleton tau L).qClosure.levelPolynomial =
      sigma.qClosure.levelPolynomial *
        (1 + Polynomial.X) ^ Fintype.card Vertex :=
  L.separatedLevelPolynomial_eq_original_mul_of_alignment
    (canonicalSeparatedSkeleton tau L)
    (canonicalSeparatedSimpleLabelData tau L)
    (canonicalSeparatedNonsimpleFreeData tau L)
    (canonicalSeparatedCoreAlignment tau L)

/-- The canonical relabeling is aligned with the identity equivalence of the
underlying triangular module category. -/
def canonicalSeparatedAlignedEquivalence
    (L : OriginalNonsimpleLabelData Nonsimple Vertex sigma) :
    IndecomposableSkeleton.AlignedEquivalence tau
      (canonicalSeparatedSkeleton tau L) where
  categoryEquiv := CategoryTheory.Equivalence.refl
  labelEquiv := (separatedCandidateEquiv tau L).symm
  objIso k := eqToIso (by simp [canonicalSeparatedSkeleton])

/-- Finiteness of the original label families forces finiteness of the
label type of every complete triangular target skeleton. -/
theorem separatedTargetIndex_finite
    [Finite Nonsimple] [Finite Vertex]
    (tau : IndecomposableSkeleton.{max u v, z, w}
      (Algebra S J) kappa)
    (L : OriginalNonsimpleLabelData Nonsimple Vertex sigma) :
    Finite kappa :=
  (separatedCandidateEquiv tau L).finite_iff.mp inferInstance

/-- The Boolean-factor identity can be stated directly for the arbitrary
target skeleton, without exposing its canonical relabeling. -/
theorem separatedTargetLevelPolynomial_eq_original_mul
    [Fintype Nonsimple] [DecidableEq Nonsimple]
    [Fintype Vertex] [DecidableEq Vertex]
    [Finite kappa]
    (L : OriginalNonsimpleLabelData Nonsimple Vertex sigma) :
    tau.qClosure.levelPolynomial =
      sigma.qClosure.levelPolynomial *
        (1 + Polynomial.X) ^ Fintype.card Vertex := by
  rw [(canonicalSeparatedAlignedEquivalence tau L).quotientLevelPolynomial_eq]
  exact canonicalSeparatedLevelPolynomial_eq_original_mul tau L

/-- The canonical nonsimple/simple partition is aligned with the original
skeleton by the identity equivalence of its module category. -/
def nonsimpleSimpleAlignedEquivalence
    {R : Type u} [Ring R] [IsNoetherianRing R]
    {iota : Type z}
    (rho : IndecomposableSkeleton.{u, z, w} R iota) :
    IndecomposableSkeleton.AlignedEquivalence rho
      rho.nonsimpleSimpleSkeleton where
  categoryEquiv := CategoryTheory.Equivalence.refl
  labelEquiv := rho.nonsimpleSimpleEquiv.symm
  objIso i := eqToIso (by
    change rho.obj i =
      rho.obj (rho.nonsimpleSimpleEquiv
        (rho.nonsimpleSimpleEquiv.symm i))
    rw [Equiv.apply_symm_apply])

/-- Paper-facing unlabeled form of the square-zero Boolean factor: an
arbitrary original skeleton and an arbitrary triangular target skeleton are
compared using only their canonical indecomposable partitions. -/
theorem separatedTargetLevelPolynomial_eq_original_mul_ofSkeleton
    {iota : Type z} [Finite iota]
    (rho : IndecomposableSkeleton.{max u v, z, w}
      (TrivSqZeroExt S J) iota)
    {kappa : Type*} [Finite kappa]
    (tau : IndecomposableSkeleton.{max u v, _, w}
      (Algebra S J) kappa) :
    tau.qClosure.levelPolynomial =
      rho.qClosure.levelPolynomial *
        (1 + Polynomial.X) ^
          Nat.card (IndecomposableSkeleton.SimpleIndex rho) := by
  classical
  letI : Fintype iota := Fintype.ofFinite iota
  letI : Finite (IndecomposableSkeleton.NonsimpleIndex rho) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Finite (IndecomposableSkeleton.SimpleIndex rho) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype (IndecomposableSkeleton.NonsimpleIndex rho) :=
    Fintype.ofFinite _
  letI : Fintype (IndecomposableSkeleton.SimpleIndex rho) :=
    Fintype.ofFinite _
  let L := OriginalNonsimpleLabelData.ofSkeleton rho
  calc
    tau.qClosure.levelPolynomial =
        rho.nonsimpleSimpleSkeleton.qClosure.levelPolynomial *
          (1 + Polynomial.X) ^
            Nat.card (IndecomposableSkeleton.SimpleIndex rho) := by
      simpa [Nat.card_eq_fintype_card] using
        separatedTargetLevelPolynomial_eq_original_mul tau L
    _ = rho.qClosure.levelPolynomial *
          (1 + Polynomial.X) ^
            Nat.card (IndecomposableSkeleton.SimpleIndex rho) := by
      rw [← (nonsimpleSimpleAlignedEquivalence rho).quotientLevelPolynomial_eq]

/-- Representation-finiteness passes from a finite original skeleton to the
triangular separated algebra.  This is the formal version of the manuscript
argument that the separated side has the same nonsimples and only one extra
simple copy at each vertex. -/
theorem separatedAlgebra_isRepresentationFinite_of_finiteSkeleton
    {iota : Type z} [Finite iota]
    (rho : IndecomposableSkeleton.{max u v, z, w}
      (TrivSqZeroExt S J) iota)
    (hfinite : ∀ X : FGModuleCat.{w} (Algebra S J),
      IsFiniteLength (Algebra S J) X) :
    IsRepresentationFinite.{max u v, w} (Algebra S J) := by
  letI : Finite (IndecomposableSkeleton.NonsimpleIndex rho) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Finite (IndecomposableSkeleton.SimpleIndex rho) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  let tau := indecomposableSkeletonOfFiniteLength hfinite
  let L := OriginalNonsimpleLabelData.ofSkeleton rho
  exact separatedTargetIndex_finite tau L

end QuotientSubmoduleEquidistribution.RadicalSquareZero
