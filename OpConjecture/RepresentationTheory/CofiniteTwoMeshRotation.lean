import OpConjecture.RepresentationTheory.BoundaryArrowBalance
import OpConjecture.RepresentationTheory.CofiniteTwoSimpleRank

/-!
# Mesh rotation and the two categorical boundary counts

This file isolates the exact existence-level Auslander--Reiten translation
interface used in the manuscript's colevel-two argument.  From an equivalence
between nonprojective and noninjective labels which rotates irreducible
incidence, it proves equality of the categorical `beta_q` and `beta_s` pair
counts.  Under the finite-dimensional simple-rank hypotheses, it then gives
the conditional common colevel-two formula for literal additive
subcategories.
-/

noncomputable section

open CategoryTheory

namespace OpConjecture.IndecomposableSkeleton

universe uR v w

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{uR, v, w} R ι)

/-- Labels of indecomposable nonprojective objects. -/
def NonprojectiveLabel :=
  {z : ι // ¬ Projective (σ.obj z)}

/-- Labels of indecomposable noninjective objects. -/
def NoninjectiveLabel :=
  {x : ι // ¬ Injective (σ.obj x)}

/-- The exact existence-level mesh-rotation interface needed by the
colevel-two boundary argument.  Its intended `tau` sends a nonprojective
indecomposable to the left term of its almost-split sequence. -/
structure ARMeshRotationData where
  tau : σ.NonprojectiveLabel ≃ σ.NoninjectiveLabel
  incidence : ∀ (z : σ.NonprojectiveLabel) (x : ι),
    HasIrreducibleMorphism (σ.obj x) (σ.obj z.1) ↔
      HasIrreducibleMorphism (σ.obj (tau z).1) (σ.obj x)

/-- Irreducible pairs whose target is nonprojective. -/
def NonprojectiveTargetIrreduciblePair :=
  {p : ι × ι //
    ¬ Projective (σ.obj p.2) ∧
      HasIrreducibleMorphism (σ.obj p.1) (σ.obj p.2)}

/-- Irreducible pairs whose source is noninjective. -/
def NoninjectiveSourceIrreduciblePair :=
  {p : ι × ι //
    ¬ Injective (σ.obj p.1) ∧
      HasIrreducibleMorphism (σ.obj p.1) (σ.obj p.2)}

/-- Mesh rotation is a bijection from irreducible pairs ending at
nonprojectives to irreducible pairs starting at noninjectives. -/
def ARMeshRotationData.arrowEquiv
    (M : σ.ARMeshRotationData) :
    σ.NonprojectiveTargetIrreduciblePair ≃
      σ.NoninjectiveSourceIrreduciblePair where
  toFun a := by
    let z : σ.NonprojectiveLabel := ⟨a.1.2, a.2.1⟩
    exact
      ⟨((M.tau z).1, a.1.1), (M.tau z).2,
        (M.incidence z a.1.1).1 a.2.2⟩
  invFun a := by
    let x : σ.NoninjectiveLabel := ⟨a.1.1, a.2.1⟩
    let z : σ.NonprojectiveLabel := M.tau.symm x
    have htau : M.tau z = x := M.tau.apply_symm_apply x
    refine ⟨(a.1.2, z.1), z.2, ?_⟩
    apply (M.incidence z a.1.2).2
    simpa only [htau] using a.2.2
  left_inv a := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact congrArg Subtype.val
        (M.tau.symm_apply_apply ⟨a.1.2, a.2.1⟩)
  right_inv a := by
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val
        (M.tau.apply_symm_apply ⟨a.1.1, a.2.1⟩)
    · rfl

/-- Rotated quotient-boundary pairs: noninjective source and projective
target. -/
def NoninjectiveToProjectiveIrreduciblePair :=
  {p : ι × ι //
    ¬ Injective (σ.obj p.1) ∧
      Projective (σ.obj p.2) ∧
      HasIrreducibleMorphism (σ.obj p.1) (σ.obj p.2)}

/-- Inverse-rotated submodule-boundary pairs: injective source and
nonprojective target. -/
def InjectiveToNonprojectiveIrreduciblePair :=
  {p : ι × ι //
    Injective (σ.obj p.1) ∧
      ¬ Projective (σ.obj p.2) ∧
      HasIrreducibleMorphism (σ.obj p.1) (σ.obj p.2)}

/-- Restrict mesh rotation to the manuscript's quotient boundary. -/
def ARMeshRotationData.qBoundaryEquiv
    (M : σ.ARMeshRotationData) :
    σ.QIrreducibleBoundaryPair ≃
      σ.NoninjectiveToProjectiveIrreduciblePair where
  toFun a := by
    let z : σ.NonprojectiveLabel := ⟨a.1.2, a.2.2.1⟩
    exact
      ⟨((M.tau z).1, a.1.1), (M.tau z).2, a.2.1,
        (M.incidence z a.1.1).1 a.2.2.2⟩
  invFun a := by
    let x : σ.NoninjectiveLabel := ⟨a.1.1, a.2.1⟩
    let z : σ.NonprojectiveLabel := M.tau.symm x
    have htau : M.tau z = x := M.tau.apply_symm_apply x
    refine ⟨(a.1.2, z.1), a.2.2.1, z.2, ?_⟩
    apply (M.incidence z a.1.2).2
    simpa only [htau] using a.2.2.2
  left_inv a := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact congrArg Subtype.val
        (M.tau.symm_apply_apply ⟨a.1.2, a.2.2.1⟩)
  right_inv a := by
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val
        (M.tau.apply_symm_apply ⟨a.1.1, a.2.1⟩)
    · rfl

/-- Restrict inverse mesh rotation to the manuscript's submodule boundary. -/
def ARMeshRotationData.sBoundaryEquiv
    (M : σ.ARMeshRotationData) :
    σ.SIrreducibleBoundaryPair ≃
      σ.InjectiveToNonprojectiveIrreduciblePair where
  toFun a := by
    let x : σ.NoninjectiveLabel := ⟨a.1.1, a.2.1⟩
    let z : σ.NonprojectiveLabel := M.tau.symm x
    have htau : M.tau z = x := M.tau.apply_symm_apply x
    refine ⟨(a.1.2, z.1), a.2.2.1, z.2, ?_⟩
    apply (M.incidence z a.1.2).2
    simpa only [htau] using a.2.2.2
  invFun a := by
    let z : σ.NonprojectiveLabel := ⟨a.1.2, a.2.2.1⟩
    exact
      ⟨((M.tau z).1, a.1.1), (M.tau z).2, a.2.1,
        (M.incidence z a.1.1).1 a.2.2.2⟩
  left_inv a := by
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val
        (M.tau.apply_symm_apply ⟨a.1.1, a.2.1⟩)
    · rfl
  right_inv a := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact congrArg Subtype.val
        (M.tau.symm_apply_apply ⟨a.1.2, a.2.2.1⟩)

/-- One support edge for each ordered indecomposable pair carrying a
categorical irreducible morphism.  This is the pair-level model corresponding
to the manuscript's `beta` terms once categorical irreducibility is bridged
to nonvanishing of the literal radical quotient. -/
def IrreduciblePair :=
  {p : ι × ι //
    HasIrreducibleMorphism (σ.obj p.1) (σ.obj p.2)}

/-- Source label of an irreducible pair. -/
def IrreduciblePair.src (a : σ.IrreduciblePair) : ι := a.1.1

/-- Target label of an irreducible pair. -/
def IrreduciblePair.dst (a : σ.IrreduciblePair) : ι := a.1.2

section Finite

variable [Fintype ι] [DecidableEq ι]

local instance : DecidablePred (fun p : ι × ι ↦
    HasIrreducibleMorphism (σ.obj p.1) (σ.obj p.2)) := Classical.decPred _

local instance : Finite σ.IrreduciblePair :=
  Finite.of_injective Subtype.val Subtype.coe_injective

local instance : Fintype σ.IrreduciblePair := Fintype.ofFinite _

/-- The categorical projective labels, as a finset. -/
def projectiveIndices : Finset ι := by
  classical
  exact Finset.univ.filter fun p ↦ Projective (σ.obj p)

/-- The categorical injective labels, as a finset. -/
def injectiveIndices : Finset ι := by
  classical
  exact Finset.univ.filter fun i ↦ Injective (σ.obj i)

omit [DecidableEq ι] in
@[simp] theorem mem_projectiveIndices {p : ι} :
    p ∈ σ.projectiveIndices ↔ Projective (σ.obj p) := by
  classical
  simp [projectiveIndices]

omit [DecidableEq ι] in
@[simp] theorem mem_injectiveIndices {i : ι} :
    i ∈ σ.injectiveIndices ↔ Injective (σ.obj i) := by
  classical
  simp [injectiveIndices]

/-- The filtered edge set ending at a nonprojective is the relation-level
nonprojective-target pair type. -/
def nonprojectiveTargetEdgeEquiv :
    {a : σ.IrreduciblePair //
      IrreduciblePair.src (σ := σ) a ∈ (Finset.univ : Finset ι) ∧
        IrreduciblePair.dst (σ := σ) a ∈ σ.projectiveIndicesᶜ} ≃
      σ.NonprojectiveTargetIrreduciblePair where
  toFun a := by
    refine ⟨a.1.1, ?_, a.1.2⟩
    simpa only [IrreduciblePair.dst, Finset.mem_compl,
      mem_projectiveIndices] using a.2.2
  invFun a := by
    refine ⟨⟨a.1, a.2.2⟩, Finset.mem_univ _, ?_⟩
    simpa only [IrreduciblePair.dst, Finset.mem_compl,
      mem_projectiveIndices] using a.2.1
  left_inv a := by aesop
  right_inv a := by aesop

/-- The filtered edge set starting at a noninjective is the relation-level
noninjective-source pair type. -/
def noninjectiveSourceEdgeEquiv :
    {a : σ.IrreduciblePair //
      IrreduciblePair.src (σ := σ) a ∈ σ.injectiveIndicesᶜ ∧
        IrreduciblePair.dst (σ := σ) a ∈ (Finset.univ : Finset ι)} ≃
      σ.NoninjectiveSourceIrreduciblePair where
  toFun a := by
    refine ⟨a.1.1, ?_, a.1.2⟩
    simpa only [IrreduciblePair.src, Finset.mem_compl,
      mem_injectiveIndices] using a.2.1
  invFun a := by
    refine ⟨⟨a.1, a.2.2⟩, ?_, Finset.mem_univ _⟩
    simpa only [IrreduciblePair.src, Finset.mem_compl,
      mem_injectiveIndices] using a.2.1
  left_inv a := by aesop
  right_inv a := by aesop

/-- The left mixed filtered edge set is the rotated quotient-boundary pair
type. -/
def noninjectiveToProjectiveEdgeEquiv :
    {a : σ.IrreduciblePair //
      IrreduciblePair.src (σ := σ) a ∈ σ.injectiveIndicesᶜ ∧
        IrreduciblePair.dst (σ := σ) a ∈ σ.projectiveIndices} ≃
      σ.NoninjectiveToProjectiveIrreduciblePair where
  toFun a := by
    refine ⟨a.1.1, ?_, ?_, a.1.2⟩
    · simpa only [IrreduciblePair.src, Finset.mem_compl,
        mem_injectiveIndices] using a.2.1
    · simpa only [IrreduciblePair.dst,
        mem_projectiveIndices] using a.2.2
  invFun a := by
    refine ⟨⟨a.1, a.2.2.2⟩, ?_, ?_⟩
    · simpa only [IrreduciblePair.src, Finset.mem_compl,
        mem_injectiveIndices] using a.2.1
    · simpa only [IrreduciblePair.dst,
        mem_projectiveIndices] using a.2.2.1
  left_inv a := by aesop
  right_inv a := by aesop

/-- The right mixed filtered edge set is the inverse-rotated
submodule-boundary pair type. -/
def injectiveToNonprojectiveEdgeEquiv :
    {a : σ.IrreduciblePair //
      IrreduciblePair.src (σ := σ) a ∈ σ.injectiveIndices ∧
        IrreduciblePair.dst (σ := σ) a ∈ σ.projectiveIndicesᶜ} ≃
      σ.InjectiveToNonprojectiveIrreduciblePair where
  toFun a := by
    refine ⟨a.1.1, ?_, ?_, a.1.2⟩
    · simpa only [IrreduciblePair.src,
        mem_injectiveIndices] using a.2.1
    · simpa only [IrreduciblePair.dst, Finset.mem_compl,
        mem_projectiveIndices] using a.2.2
  invFun a := by
    refine ⟨⟨a.1, a.2.2.2⟩, ?_, ?_⟩
    · simpa only [IrreduciblePair.src,
        mem_injectiveIndices] using a.2.1
    · simpa only [IrreduciblePair.dst, Finset.mem_compl,
        mem_projectiveIndices] using a.2.2.1
  left_inv a := by aesop
  right_inv a := by aesop

/-- The mesh-rotation datum supplies exactly the hypothesis consumed by
`BoundaryArrowBalance`. -/
theorem ARMeshRotationData.edgeCount_mesh
    (M : σ.ARMeshRotationData) :
    OpConjecture.BoundaryArrowBalance.edgeCount
        (IrreduciblePair.src (σ := σ))
        (IrreduciblePair.dst (σ := σ))
        Finset.univ σ.projectiveIndicesᶜ =
      OpConjecture.BoundaryArrowBalance.edgeCount
        (IrreduciblePair.src (σ := σ))
        (IrreduciblePair.dst (σ := σ))
        σ.injectiveIndicesᶜ Finset.univ := by
  classical
  rw [OpConjecture.BoundaryArrowBalance.edgeCount,
    OpConjecture.BoundaryArrowBalance.edgeCount,
    ← Fintype.card_subtype,
    ← Fintype.card_subtype]
  exact Fintype.card_congr
    (σ.nonprojectiveTargetEdgeEquiv.trans
      (M.arrowEquiv.trans σ.noninjectiveSourceEdgeEquiv.symm))

/-- The left mixed edge count is the cardinality of the rotated quotient
boundary. -/
theorem edgeCount_noninjective_projective_eq_natCard :
    OpConjecture.BoundaryArrowBalance.edgeCount
        (IrreduciblePair.src (σ := σ))
        (IrreduciblePair.dst (σ := σ))
        σ.injectiveIndicesᶜ σ.projectiveIndices =
      Nat.card σ.NoninjectiveToProjectiveIrreduciblePair := by
  classical
  rw [OpConjecture.BoundaryArrowBalance.edgeCount,
    ← Fintype.card_subtype,
    ← Nat.card_eq_fintype_card]
  exact Nat.card_congr σ.noninjectiveToProjectiveEdgeEquiv

/-- The right mixed edge count is the cardinality of the inverse-rotated
submodule boundary. -/
theorem edgeCount_injective_nonprojective_eq_natCard :
    OpConjecture.BoundaryArrowBalance.edgeCount
        (IrreduciblePair.src (σ := σ))
        (IrreduciblePair.dst (σ := σ))
        σ.injectiveIndices σ.projectiveIndicesᶜ =
      Nat.card σ.InjectiveToNonprojectiveIrreduciblePair := by
  classical
  rw [OpConjecture.BoundaryArrowBalance.edgeCount,
    ← Fintype.card_subtype,
    ← Nat.card_eq_fintype_card]
  exact Nat.card_congr σ.injectiveToNonprojectiveEdgeEquiv

/-- The manuscript's two irreducible boundary-pair counts agree from the
exact existence-level mesh-rotation interface. -/
theorem ARMeshRotationData.natCard_QIrreducibleBoundaryPair_eq_natCard_SIrreducibleBoundaryPair
    (M : σ.ARMeshRotationData) :
    Nat.card σ.QIrreducibleBoundaryPair =
      Nat.card σ.SIrreducibleBoundaryPair := by
  classical
  have hmixed :=
    OpConjecture.BoundaryArrowBalance.mixedBoundary_eq_of_meshRotation
      (IrreduciblePair.src (σ := σ))
      (IrreduciblePair.dst (σ := σ))
      σ.projectiveIndices σ.injectiveIndices
      M.edgeCount_mesh
  calc
    Nat.card σ.QIrreducibleBoundaryPair =
        Nat.card σ.NoninjectiveToProjectiveIrreduciblePair :=
      Nat.card_congr M.qBoundaryEquiv
    _ = OpConjecture.BoundaryArrowBalance.edgeCount
          (IrreduciblePair.src (σ := σ))
          (IrreduciblePair.dst (σ := σ))
          σ.injectiveIndicesᶜ σ.projectiveIndices :=
      σ.edgeCount_noninjective_projective_eq_natCard.symm
    _ = OpConjecture.BoundaryArrowBalance.edgeCount
          (IrreduciblePair.src (σ := σ))
          (IrreduciblePair.dst (σ := σ))
          σ.injectiveIndices σ.projectiveIndicesᶜ := hmixed
    _ = Nat.card σ.InjectiveToNonprojectiveIrreduciblePair :=
      σ.edgeCount_injective_nonprojective_eq_natCard
    _ = Nat.card σ.SIrreducibleBoundaryPair :=
      (Nat.card_congr M.sBoundaryEquiv).symm

end Finite

end OpConjecture.IndecomposableSkeleton

namespace OpConjecture.IndecomposableSkeleton

universe u v

section FiniteDimensionalCorollary

variable {K R : Type u} [Field K] [Ring R] [Algebra K R]
  [FiniteDimensional K R] [IsNoetherianRing R]
  [IsNoetherianRing Rᵐᵒᵖ]
  {ι : Type v} [Fintype ι] [DecidableEq ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)
  [∀ i : ι, Module K (σ.obj i)]
  [∀ i : ι, IsScalarTower K R (σ.obj i)]
  [∀ i : ι, FiniteDimensional K (σ.obj i)]

include K in
/-- Under mesh rotation, the quotient and submodule cofinite-two counts
agree in the finite-dimensional simple-rank setting. -/
theorem ARMeshRotationData.qCofiniteTwoCount_eq_sCofiniteTwoCount
    (M : σ.ARMeshRotationData) :
    σ.qClosure.cofiniteTwoCount = σ.sClosure.cofiniteTwoCount := by
  calc
    σ.qClosure.cofiniteTwoCount =
        Nat.choose (Nat.card σ.SimpleIndex) 2 +
          Nat.card σ.QIrreducibleBoundaryPair :=
      σ.qCofiniteTwoCount_eq_choose_simpleIndex_add_irreducibleBoundary
        (K := K)
    _ = Nat.choose (Nat.card σ.SimpleIndex) 2 +
          Nat.card σ.SIrreducibleBoundaryPair := by
      rw [M.natCard_QIrreducibleBoundaryPair_eq_natCard_SIrreducibleBoundaryPair]
    _ = σ.sClosure.cofiniteTwoCount :=
      (σ.sCofiniteTwoCount_eq_choose_simpleIndex_add_irreducibleBoundary
        (K := K)).symm

include K in
/-- Under mesh rotation, literal quotient-closed and subobject-closed
additive subcategories have the same `(Nat.card ι - 2)` level count. -/
theorem ARMeshRotationData.literalLevelCount_card_sub_two_eq
    (M : σ.ARMeshRotationData) (hcard : 2 ≤ Nat.card ι) :
    σ.literalQuotientLevelCount (Nat.card ι - 2) =
      σ.literalSubobjectLevelCount (Nat.card ι - 2) := by
  calc
    σ.literalQuotientLevelCount (Nat.card ι - 2) =
        Nat.choose (Nat.card σ.SimpleIndex) 2 +
          Nat.card σ.QIrreducibleBoundaryPair :=
      σ.literalQuotientLevelCount_card_sub_two_eq_choose_simpleIndex_add_irreducibleBoundary
        (K := K) hcard
    _ = Nat.choose (Nat.card σ.SimpleIndex) 2 +
          Nat.card σ.SIrreducibleBoundaryPair := by
      rw [M.natCard_QIrreducibleBoundaryPair_eq_natCard_SIrreducibleBoundaryPair]
    _ = σ.literalSubobjectLevelCount (Nat.card ι - 2) :=
      (σ.literalSubobjectLevelCount_card_sub_two_eq_choose_simpleIndex_add_irreducibleBoundary
        (K := K) hcard).symm

include K in
/-- Conditional finite-dimensional form of the manuscript's colevel-two
corollary: the two literal counts agree and have the common simple-rank plus
`beta_q` value. -/
theorem ARMeshRotationData.literalCofiniteTwo_formula
    (M : σ.ARMeshRotationData) (hcard : 2 ≤ Nat.card ι) :
    σ.literalQuotientLevelCount (Nat.card ι - 2) =
        σ.literalSubobjectLevelCount (Nat.card ι - 2) ∧
      σ.literalQuotientLevelCount (Nat.card ι - 2) =
        Nat.choose (Nat.card σ.SimpleIndex) 2 +
          Nat.card σ.QIrreducibleBoundaryPair := by
  exact
    ⟨ARMeshRotationData.literalLevelCount_card_sub_two_eq
        (K := K) σ M hcard,
      σ.literalQuotientLevelCount_card_sub_two_eq_choose_simpleIndex_add_irreducibleBoundary
        (K := K) hcard⟩

end FiniteDimensionalCorollary

end OpConjecture.IndecomposableSkeleton
