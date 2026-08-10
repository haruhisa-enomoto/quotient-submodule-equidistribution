import QuotientSubmoduleEquidistribution.RepresentationTheory.FiniteARTranslationData
import QuotientSubmoduleEquidistribution.RepresentationTheory.NakayamaRepresentationFiniteBridge

/-!
# Boundary-pair finiteness from local almost-split maps

This file proves finiteness of the irreducible boundary terms without
assuming that the complete indecomposable skeleton is finite.  A minimal
right almost-split decomposition has only finitely many indecomposable
summands, so it has only finitely many irreducible sources.  Applying this
locally at the finite projective or injective boundary controls the two
boundary-pair types.

On the quotient side, Auslander--Reiten translation rotates an irreducible
map from a projective into an irreducible map to that projective.  Only
injectivity of the translation is needed; no global surjectivity or finite
skeleton is used.  On the submodule side, the supplied right almost-split
map ending at each injective controls the incoming irreducible maps directly.
-/

noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

universe uR uι

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {ι : Type uι}
  (σ : IndecomposableSkeleton.{uR, uι, uR} R ι)

namespace MinimalRightAlmostSplitDecomposition

/-- A finite middle decomposition makes the type of irreducible sources of
its endpoint finite. -/
theorem finite_irreducibleSourceLabel
    {z : ι} (A : σ.MinimalRightAlmostSplitDecomposition z) :
    Finite {x : ι //
      HasIrreducibleMorphism (σ.obj x) (σ.obj z)} := by
  let occurrence : A.index →
      {x : ι // HasIrreducibleMorphism (σ.obj x) (σ.obj z)} :=
    fun t ↦
      ⟨A.label t,
        (A.summandIrreducibleCorrespondence (A.label t)).1 ⟨t, rfl⟩⟩
  apply Finite.of_surjective occurrence
  rintro ⟨x, hx⟩
  obtain ⟨t, ht⟩ :=
    (A.summandIrreducibleCorrespondence x).2 hx
  refine ⟨t, Subtype.ext ?_⟩
  exact ht

end MinimalRightAlmostSplitDecomposition

namespace FiniteARTranslationData

variable (D : σ.FiniteARTranslationData)

include D in
/-- Local right almost-split decompositions at all projective labels make
the quotient irreducible-boundary type finite.  AR translation rotates a
boundary arrow `p ⟶ z` to an incoming arrow `τz ⟶ p`; its injectivity
recovers `z` from the rotated source. -/
theorem finite_QIrreducibleBoundaryPair_of_projectiveRightAR
    (projectiveRightAR :
      ∀ p : {i : ι // Projective (σ.obj i)},
        σ.MinimalRightAlmostSplitDecomposition p.1) :
    Finite σ.QIrreducibleBoundaryPair := by
  letI : Fintype {i : ι // Projective (σ.obj i)} :=
    (QuotientSubmoduleEquidistribution.NakayamaRepresentationFiniteBridge.finite_projectiveLabels
      σ).fintype
  letI : ∀ p : {i : ι // Projective (σ.obj i)},
      Finite {x : ι //
        HasIrreducibleMorphism (σ.obj x) (σ.obj p.1)} :=
    fun p ↦ (projectiveRightAR p).finite_irreducibleSourceLabel
  let code : σ.QIrreducibleBoundaryPair →
      Σ p : {i : ι // Projective (σ.obj i)},
        {x : ι // HasIrreducibleMorphism (σ.obj x) (σ.obj p.1)} :=
    fun a ↦ by
      let z : σ.NonprojectiveLabel := ⟨a.1.2, a.2.2.1⟩
      exact
        ⟨⟨a.1.1, a.2.1⟩,
          ⟨(arTranslation σ D z).1,
            (arTranslation_incidence σ D z a.1.1).1 a.2.2.2⟩⟩
  apply Finite.of_injective code
  intro a b hab
  let za : σ.NonprojectiveLabel := ⟨a.1.2, a.2.2.1⟩
  let zb : σ.NonprojectiveLabel := ⟨b.1.2, b.2.2.1⟩
  have hp : a.1.1 = b.1.1 := by
    simpa only [code] using congrArg (fun c ↦ c.1.1) hab
  have hτval : (arTranslation σ D za).1 =
      (arTranslation σ D zb).1 := by
    simpa only [code, za, zb] using congrArg (fun c ↦ c.2.1) hab
  have hτ : arTranslation σ D za = arTranslation σ D zb :=
    Subtype.ext hτval
  have hz : za = zb := arTranslation_injective σ D hτ
  apply Subtype.ext
  exact Prod.ext hp (congrArg Subtype.val hz)

include D in
/-- Local right almost-split decompositions at all injective labels make
the submodule irreducible-boundary type finite.  Finiteness of the injective
boundary is transported from the finite projective boundary by `D.boundary`.
-/
theorem finite_SIrreducibleBoundaryPair_of_injectiveRightAR
    (injectiveRightAR :
      ∀ i : {j : ι // Injective (σ.obj j)},
        σ.MinimalRightAlmostSplitDecomposition i.1) :
    Finite σ.SIrreducibleBoundaryPair := by
  letI : Fintype {i : ι // Projective (σ.obj i)} :=
    (QuotientSubmoduleEquidistribution.NakayamaRepresentationFiniteBridge.finite_projectiveLabels
      σ).fintype
  letI : Finite {i : ι // Injective (σ.obj i)} :=
    Finite.of_equiv {i : ι // Projective (σ.obj i)} D.boundary
  letI : ∀ i : {j : ι // Injective (σ.obj j)},
      Finite {x : ι //
        HasIrreducibleMorphism (σ.obj x) (σ.obj i.1)} :=
    fun i ↦ (injectiveRightAR i).finite_irreducibleSourceLabel
  let code : σ.SIrreducibleBoundaryPair →
      Σ i : {j : ι // Injective (σ.obj j)},
        {x : ι // HasIrreducibleMorphism (σ.obj x) (σ.obj i.1)} :=
    fun a ↦ ⟨⟨a.1.2, a.2.2.1⟩, ⟨a.1.1, a.2.2.2⟩⟩
  apply Finite.of_injective code
  intro a b hab
  apply Subtype.ext
  apply Prod.ext
  · simpa only [code] using congrArg (fun c ↦ c.2.1) hab
  · simpa only [code] using congrArg (fun c ↦ c.1.1) hab

include D in
/-- Literal `rad / rad²` quotient-boundary finiteness under the same local
right almost-split input. -/
theorem finite_QRadicalQuotientBoundaryPair_of_projectiveRightAR
    (projectiveRightAR :
      ∀ p : {i : ι // Projective (σ.obj i)},
        σ.MinimalRightAlmostSplitDecomposition p.1) :
    Finite σ.QRadicalQuotientBoundaryPair := by
  letI : Finite σ.QIrreducibleBoundaryPair :=
    finite_QIrreducibleBoundaryPair_of_projectiveRightAR
      σ D projectiveRightAR
  exact Finite.of_equiv σ.QIrreducibleBoundaryPair
    σ.qRadicalQuotientBoundaryPairEquivQIrreducibleBoundaryPair.symm

include D in
/-- Literal `rad / rad²` submodule-boundary finiteness under the same local
right almost-split input. -/
theorem finite_SRadicalQuotientBoundaryPair_of_injectiveRightAR
    (injectiveRightAR :
      ∀ i : {j : ι // Injective (σ.obj j)},
        σ.MinimalRightAlmostSplitDecomposition i.1) :
    Finite σ.SRadicalQuotientBoundaryPair := by
  letI : Finite σ.SIrreducibleBoundaryPair :=
    finite_SIrreducibleBoundaryPair_of_injectiveRightAR
      σ D injectiveRightAR
  exact Finite.of_equiv σ.SIrreducibleBoundaryPair
    σ.sRadicalQuotientBoundaryPairEquivSIrreducibleBoundaryPair.symm

end FiniteARTranslationData

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
