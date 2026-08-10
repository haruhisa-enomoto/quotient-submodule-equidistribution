import QuotientSubmoduleEquidistribution.RepresentationTheory.AlmostSplitUniqueness
import QuotientSubmoduleEquidistribution.RepresentationTheory.CofiniteTwoMeshRotation
import QuotientSubmoduleEquidistribution.RepresentationTheory.FiniteTypeAlmostSplit
import Mathlib.Data.Fintype.EquivFin

/-!
# Auslander--Reiten translation on a finite indecomposable skeleton

For a finite-dimensional algebra with a finite complete indecomposable
skeleton, this file chooses a minimal right almost-split map at every
nonprojective vertex and defines its Auslander--Reiten translate to be the
chosen skeleton representative of the kernel.

Kernel-sequence uniqueness makes this label map injective.  Equality of the
projective and injective boundary cardinalities then makes it an equivalence
between nonprojective and noninjective labels.  The two summand--irreducible
correspondences for the common middle term prove mesh incidence, yielding
the `ARMeshRotationData` consumed by the colevel-two count.

No concrete algebra presentation or module classification is used.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

universe u v

variable {K R : Type u} [Field K] [Ring R] [Algebra K R]
  [FiniteDimensional K R] [IsNoetherianRing R]
  [IsNoetherianRing Rᵐᵒᵖ]
  {ι : Type v} [Fintype ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)

local instance : Finite σ.NonprojectiveLabel :=
  Finite.of_injective Subtype.val Subtype.val_injective
local instance : Finite σ.NoninjectiveLabel :=
  Finite.of_injective Subtype.val Subtype.val_injective
local instance : Fintype σ.NonprojectiveLabel := Fintype.ofFinite _
local instance : Fintype σ.NoninjectiveLabel := Fintype.ofFinite _

/-- A chosen minimal right almost-split decomposition at a nonprojective
vertex. -/
def chosenRightAR (z : σ.NonprojectiveLabel) :
    σ.MinimalRightAlmostSplitDecomposition z.1 :=
  Classical.choice
    (σ.minimalRightAlmostSplitDecomposition_nonempty_of_finiteDimensional
      K z.1)

local instance chosenRightAR_epi (z : σ.NonprojectiveLabel) :
    Epi (σ.chosenRightAR (K := K) z).map :=
  QuotientSubmoduleEquidistribution.IndecomposableSkeleton.IsRightAlmostSplit.epi_of_not_projective_obj
    σ (σ.chosenRightAR (K := K) z).map
      (σ.chosenRightAR (K := K) z).rightAlmostSplit z.2

omit [IsNoetherianRing Rᵐᵒᵖ] in
/-- The kernel package supplied by the chosen right AR map. -/
theorem chosenRightAR_kernel_ar_sequence (z : σ.NonprojectiveLabel) :
    IsLeftAlmostSplit (kernel.ι (σ.chosenRightAR (K := K) z).map) ∧
      IsLeftMinimal (kernel.ι (σ.chosenRightAR (K := K) z).map) ∧
      QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R
        (kernel (σ.chosenRightAR (K := K) z).map : FGModuleCat.{u} R) ∧
      ¬ Injective (kernel (σ.chosenRightAR (K := K) z).map) :=
  QuotientSubmoduleEquidistribution.IndecomposableSkeleton.MinimalRightAlmostSplitDecomposition.kernel_ar_sequence
    (σ := σ) (σ.chosenRightAR (K := K) z) z.2

/-- Skeleton label of the kernel of the chosen right AR epimorphism. -/
def arTranslationLabel (z : σ.NonprojectiveLabel) : ι :=
  Classical.choose
    (σ.complete (kernel (σ.chosenRightAR (K := K) z).map)
      (σ.chosenRightAR_kernel_ar_sequence (K := K) z).2.2.1)

/-- The chosen kernel-to-skeleton isomorphism. -/
def arTranslationKernelIso (z : σ.NonprojectiveLabel) :
    kernel (σ.chosenRightAR (K := K) z).map ≅
      σ.obj (σ.arTranslationLabel (K := K) z) :=
  (Classical.choose_spec
    (σ.complete (kernel (σ.chosenRightAR (K := K) z).map)
      (σ.chosenRightAR_kernel_ar_sequence (K := K) z).2.2.1)).some

/-- Auslander--Reiten translation as a map from nonprojective to
noninjective skeleton labels. -/
def arTranslation (z : σ.NonprojectiveLabel) :
    σ.NoninjectiveLabel :=
  ⟨σ.arTranslationLabel (K := K) z, by
    intro h
    apply (σ.chosenRightAR_kernel_ar_sequence (K := K) z).2.2.2
    exact Injective.of_iso (σ.arTranslationKernelIso (K := K) z).symm h⟩

/-- The kernel inclusion rewritten with its chosen skeleton representative
as source. -/
def arKernelMap (z : σ.NonprojectiveLabel) :
    σ.obj (σ.arTranslation (K := K) z).1 ⟶
      (σ.chosenRightAR (K := K) z).middle :=
  (σ.arTranslationKernelIso (K := K) z).inv ≫
    kernel.ι (σ.chosenRightAR (K := K) z).map

omit [IsNoetherianRing Rᵐᵒᵖ] in
/-- The transported kernel inclusion is left almost split. -/
theorem arKernelMap_leftAlmostSplit (z : σ.NonprojectiveLabel) :
    IsLeftAlmostSplit (σ.arKernelMap (K := K) z) :=
  (σ.chosenRightAR_kernel_ar_sequence (K := K) z).1.precomp_iso
    (σ.arTranslationKernelIso (K := K) z).symm

omit [IsNoetherianRing Rᵐᵒᵖ] in
/-- The transported kernel inclusion is left minimal. -/
theorem arKernelMap_leftMinimal (z : σ.NonprojectiveLabel) :
    IsLeftMinimal (σ.arKernelMap (K := K) z) :=
  (σ.chosenRightAR_kernel_ar_sequence (K := K) z).2.1.precomp_iso
    (σ.arTranslationKernelIso (K := K) z).symm

omit [IsNoetherianRing Rᵐᵒᵖ] in
/-- Equality of AR-translation labels identifies the original
nonprojective endpoints. -/
theorem arTranslation_injective :
    Function.Injective (σ.arTranslation (K := K)) := by
  intro z₁ z₂ hτ
  let hval : (σ.arTranslation (K := K) z₁).1 =
      (σ.arTranslation (K := K) z₂).1 :=
    congrArg Subtype.val hτ
  let eobj : σ.obj (σ.arTranslation (K := K) z₁).1 ≅
      σ.obj (σ.arTranslation (K := K) z₂).1 :=
    eqToIso (congrArg σ.obj hval)
  let ek : kernel (σ.chosenRightAR (K := K) z₁).map ≅
      kernel (σ.chosenRightAR (K := K) z₂).map :=
    (σ.arTranslationKernelIso (K := K) z₁).trans
      (eobj.trans (σ.arTranslationKernelIso (K := K) z₂).symm)
  let k₁' : kernel (σ.chosenRightAR (K := K) z₂).map ⟶
      (σ.chosenRightAR (K := K) z₁).middle :=
    ek.inv ≫ kernel.ι (σ.chosenRightAR (K := K) z₁).map
  have hk₁as : IsLeftAlmostSplit k₁' :=
    (σ.chosenRightAR_kernel_ar_sequence (K := K) z₁).1.precomp_iso ek.symm
  have hk₁min : IsLeftMinimal k₁' :=
    (σ.chosenRightAR_kernel_ar_sequence (K := K) z₁).2.1.precomp_iso ek.symm
  obtain ⟨emid, hemid⟩ := exists_leftAlmostSplit_middleIso
    hk₁as hk₁min
    (σ.chosenRightAR_kernel_ar_sequence (K := K) z₂).1
    (σ.chosenRightAR_kernel_ar_sequence (K := K) z₂).2.1
  let ec : cokernel k₁' ≅
      cokernel (kernel.ι (σ.chosenRightAR (K := K) z₂).map) :=
    cokernel.mapIso k₁'
      (kernel.ι (σ.chosenRightAR (K := K) z₂).map)
      (Iso.refl (kernel (σ.chosenRightAR (K := K) z₂).map)) emid
      (by simpa using hemid)
  let ec₁ : cokernel k₁' ≅
      cokernel (kernel.ι (σ.chosenRightAR (K := K) z₁).map) :=
    cokernel.mapIso k₁'
      (kernel.ι (σ.chosenRightAR (K := K) z₁).map)
      ek.symm (Iso.refl (σ.chosenRightAR (K := K) z₁).middle)
      (by simp [k₁'])
  let e₁ : cokernel k₁' ≅ σ.obj z₁.1 :=
    ec₁.trans (cokernelKernelIsoTarget (σ.chosenRightAR (K := K) z₁).map)
  let e₂ : cokernel (kernel.ι (σ.chosenRightAR (K := K) z₂).map) ≅
      σ.obj z₂.1 :=
    cokernelKernelIsoTarget (σ.chosenRightAR (K := K) z₂).map
  apply Subtype.ext
  apply σ.eq_of_iso
  exact ⟨e₁.symm.trans (ec.trans e₂)⟩

include K in
/-- The nonprojective and noninjective portions of a finite skeleton have
the same cardinality. -/
theorem card_nonprojectiveLabel_eq_card_noninjectiveLabel :
    Fintype.card σ.NonprojectiveLabel =
      Fintype.card σ.NoninjectiveLabel := by
  classical
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
  change Nat.card {i : ι // ¬ Projective (σ.obj i)} =
    Nat.card {i : ι // ¬ Injective (σ.obj i)}
  letI : Finite {i : ι // Projective (σ.obj i)} :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Finite {i : ι // Injective (σ.obj i)} :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype {i : ι // Projective (σ.obj i)} := Fintype.ofFinite _
  letI : Fintype {i : ι // Injective (σ.obj i)} := Fintype.ofFinite _
  have hboundaryNat :
      Nat.card {i : ι // Projective (σ.obj i)} =
        Nat.card {i : ι // Injective (σ.obj i)} := by
    simpa [QuotientSubmoduleEquidistribution.RingelStable.projectiveSet,
        QuotientSubmoduleEquidistribution.RingelStable.injectiveSet] using
      Nat.card_congr
        (QuotientSubmoduleEquidistribution.RingelStable.projectiveInjectiveLabelEquiv
          (R := R) K σ)
  have hboundary :
      Fintype.card {i : ι // Projective (σ.obj i)} =
        Fintype.card {i : ι // Injective (σ.obj i)} := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hboundaryNat
  have hcomplement := Fintype.card_compl_eq_card_compl
    (fun i : ι ↦ Projective (σ.obj i))
    (fun i : ι ↦ Injective (σ.obj i)) hboundary
  simpa only [← Nat.card_eq_fintype_card] using hcomplement

/-- Auslander--Reiten translation is an equivalence between nonprojective
and noninjective labels. -/
def arTranslationEquiv :
    σ.NonprojectiveLabel ≃ σ.NoninjectiveLabel := by
  classical
  exact Equiv.ofBijective (σ.arTranslation (K := K))
    ((Fintype.bijective_iff_injective_and_card
      (σ.arTranslation (K := K))).2
        ⟨σ.arTranslation_injective (K := K),
          σ.card_nonprojectiveLabel_eq_card_noninjectiveLabel (K := K)⟩)

omit [IsNoetherianRing Rᵐᵒᵖ] in
/-- AR translation rotates irreducible incidence.  Both directions are the
summand correspondences for the two minimal maps in the same short exact
sequence. -/
theorem arTranslation_incidence
    (z : σ.NonprojectiveLabel) (x : ι) :
    HasIrreducibleMorphism (σ.obj x) (σ.obj z.1) ↔
      HasIrreducibleMorphism (σ.obj (σ.arTranslation (K := K) z).1)
        (σ.obj x) := by
  let AR := σ.chosenRightAR (K := K) z
  let A := MinimalRightAlmostSplitDecomposition.ofMap σ
    AR.map AR.finiteLength AR.rightAlmostSplit AR.rightMinimal
  let B := MinimalLeftAlmostSplitDecomposition.ofMap σ
    (σ.arKernelMap (K := K) z) AR.finiteLength
    (σ.arKernelMap_leftAlmostSplit (K := K) z)
    (σ.arKernelMap_leftMinimal (K := K) z)
  exact (A.summandIrreducibleCorrespondence x).symm.trans
    (B.summandIrreducibleCorrespondence x)

/-- The actual mesh-rotation data for the finite complete skeleton of a
finite-dimensional algebra. -/
def finiteDimensionalARMeshRotationData : σ.ARMeshRotationData where
  tau := σ.arTranslationEquiv (K := K)
  incidence := by
    intro z x
    exact σ.arTranslation_incidence (K := K) z x

include K in
/-- The two categorical irreducible boundary-pair counts agree for the
finite complete skeleton of a finite-dimensional algebra. -/
theorem natCard_QIrreducibleBoundaryPair_eq_natCard_SIrreducibleBoundaryPair :
    Nat.card σ.QIrreducibleBoundaryPair =
      Nat.card σ.SIrreducibleBoundaryPair := by
  letI : DecidableEq ι := Classical.decEq ι
  exact
    ARMeshRotationData.natCard_QIrreducibleBoundaryPair_eq_natCard_SIrreducibleBoundaryPair
      (σ := σ) (σ.finiteDimensionalARMeshRotationData (K := K))

include K in
/-- The manuscript's literal radical-quotient boundary terms satisfy
`beta_q = beta_s` for a finite complete skeleton of a finite-dimensional
algebra. -/
theorem
    natCard_QRadicalQuotientBoundaryPair_eq_natCard_SRadicalQuotientBoundaryPair :
    Nat.card σ.QRadicalQuotientBoundaryPair =
      Nat.card σ.SRadicalQuotientBoundaryPair := by
  calc
    Nat.card σ.QRadicalQuotientBoundaryPair =
        Nat.card σ.QIrreducibleBoundaryPair :=
      σ.natCard_QRadicalQuotientBoundaryPair_eq_natCard_QIrreducibleBoundaryPair
    _ = Nat.card σ.SIrreducibleBoundaryPair :=
      σ.natCard_QIrreducibleBoundaryPair_eq_natCard_SIrreducibleBoundaryPair
        (K := K)
    _ = Nat.card σ.SRadicalQuotientBoundaryPair :=
      σ.natCard_SRadicalQuotientBoundaryPair_eq_natCard_SIrreducibleBoundaryPair.symm

include K in
/-- The quotient and submodule cofinite-two counts agree without a supplied
mesh-rotation hypothesis. -/
theorem finiteDimensional_qCofiniteTwoCount_eq_sCofiniteTwoCount :
    σ.qClosure.cofiniteTwoCount = σ.sClosure.cofiniteTwoCount := by
  letI : DecidableEq ι := Classical.decEq ι
  letI (i : ι) : Module K (σ.obj i) :=
    Module.restrictScalars K R (σ.obj i)
  letI (i : ι) : IsScalarTower K R (σ.obj i) :=
    IsScalarTower.restrictScalars K R (σ.obj i)
  letI (i : ι) : FiniteDimensional K (σ.obj i) :=
    Module.Finite.trans R (σ.obj i)
  exact
    ARMeshRotationData.qCofiniteTwoCount_eq_sCofiniteTwoCount
      (K := K) σ (σ.finiteDimensionalARMeshRotationData (K := K))

include K in
/-- Unconditional finite-dimensional form of the colevel-two equality and
categorical irreducible-boundary-pair formula on the chosen skeleton. -/
theorem finiteDimensional_literalCofiniteTwo_formula
    (hcard : 2 ≤ Nat.card ι) :
    σ.literalQuotientLevelCount (Nat.card ι - 2) =
        σ.literalSubobjectLevelCount (Nat.card ι - 2) ∧
      σ.literalQuotientLevelCount (Nat.card ι - 2) =
        Nat.choose (Nat.card σ.SimpleIndex) 2 +
          Nat.card σ.QIrreducibleBoundaryPair := by
  letI : DecidableEq ι := Classical.decEq ι
  letI (i : ι) : Module K (σ.obj i) :=
    Module.restrictScalars K R (σ.obj i)
  letI (i : ι) : IsScalarTower K R (σ.obj i) :=
    IsScalarTower.restrictScalars K R (σ.obj i)
  letI (i : ι) : FiniteDimensional K (σ.obj i) :=
    Module.Finite.trans R (σ.obj i)
  exact
    ARMeshRotationData.literalCofiniteTwo_formula
      (K := K) σ (σ.finiteDimensionalARMeshRotationData (K := K)) hcard

include K in
/-- Unconditional finite-dimensional form of the manuscript's literal
colevel-two statement: the two `rad / rad²` boundary terms agree, the two
literal levels agree, and their common value has the stated boundary
formula. -/
theorem finiteDimensional_literalRadicalQuotientCofiniteTwo_formula
    (hcard : 2 ≤ Nat.card ι) :
    Nat.card σ.QRadicalQuotientBoundaryPair =
        Nat.card σ.SRadicalQuotientBoundaryPair ∧
      σ.literalQuotientLevelCount (Nat.card ι - 2) =
          σ.literalSubobjectLevelCount (Nat.card ι - 2) ∧
        σ.literalQuotientLevelCount (Nat.card ι - 2) =
          Nat.choose (Nat.card σ.SimpleIndex) 2 +
            Nat.card σ.QRadicalQuotientBoundaryPair := by
  refine
    ⟨σ.natCard_QRadicalQuotientBoundaryPair_eq_natCard_SRadicalQuotientBoundaryPair
        (K := K), ?_⟩
  obtain ⟨hlevels, hformula⟩ :=
    σ.finiteDimensional_literalCofiniteTwo_formula (K := K) hcard
  refine ⟨hlevels, hformula.trans ?_⟩
  rw [σ.natCard_QRadicalQuotientBoundaryPair_eq_natCard_QIrreducibleBoundaryPair]

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
