import QuotientSubmoduleEquidistribution.Combinatorics.BoundaryTranslationChains
import QuotientSubmoduleEquidistribution.RepresentationTheory.CofiniteTwoMeshRotation
import QuotientSubmoduleEquidistribution.RepresentationTheory.FiniteARTranslationData

/-!
# Arrow occurrences and mesh-rotation orbits

The four-vertex reversal count uses occurrences of irreducible arrows, not
only their endpoint pairs.  Mesh rotation is a partial translation on this
finite occurrence type: it is undefined at arrows ending in projectives and
its image omits arrows starting in injectives.  This file packages the
existing AR mesh-rotation equivalence in exactly that boundary-chain form.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

universe u v w

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} [Fintype ι] [DecidableEq ι]
  (σ : IndecomposableSkeleton.{u, v, w} R ι)

namespace FiniteARTranslationData

variable (AR : σ.FiniteARTranslationData)

/-- AR translation as a finite partial translation from the projective
boundary to the injective boundary.  Its successor is inverse AR
translation, matching the manuscript's projective-to-injective chain
orientation. -/
def vertexOrbitData :
    QuotientSubmoduleEquidistribution.BoundaryTranslationChains.Data ι
      (fun p ↦ Projective (σ.obj p))
      (fun i ↦ Injective (σ.obj i)) where
  tau := AR.arTranslationEquiv σ

/-- Length of the projective-to-injective translation chain starting at a
projective label. -/
def vertexChainLength
    (p : ι) (hp : Projective (σ.obj p)) : ℕ :=
  (AR.vertexOrbitData σ).firstTargetIndex p hp

/-- The label at a specified position of the projective-to-injective
translation chain. -/
def vertexChainAt (p : ι) (n : ℕ) : ι :=
  (AR.vertexOrbitData σ).successor^[n] p

omit [DecidableEq ι] in
/-- The terminal label of a projective-starting translation chain is
injective. -/
theorem vertexChainAt_length_injective
    (p : ι) (hp : Projective (σ.obj p)) :
    Injective (σ.obj
      (AR.vertexChainAt σ p (AR.vertexChainLength σ p hp))) :=
  (AR.vertexOrbitData σ).firstTargetIndex_spec p hp

/-- Following translation chains gives the canonical equivalence between
projective and injective boundary labels. -/
def projectiveLabelEquivInjectiveLabel :
    {p : ι // Projective (σ.obj p)} ≃
      {i : ι // Injective (σ.obj i)} :=
  (AR.vertexOrbitData σ).boundaryEndpointEquiv

omit [DecidableEq ι] in
/-- The endpoint equivalence evaluates to the terminal chain label. -/
@[simp]
theorem projectiveLabelEquivInjectiveLabel_apply
    (p : {p : ι // Projective (σ.obj p)}) :
    (AR.projectiveLabelEquivInjectiveLabel σ p).1 =
      AR.vertexChainAt σ p.1 (AR.vertexChainLength σ p.1 p.2) := by
  rfl

end FiniteARTranslationData

namespace ARMeshRotationData

variable (M : σ.ARMeshRotationData)

noncomputable instance irreduciblePairFinite :
    Finite σ.IrreduciblePair :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance irreduciblePairFintype :
    Fintype σ.IrreduciblePair := Fintype.ofFinite _

/-- Reassociate an irreducible occurrence with a nonprojective target into
the domain type of mesh rotation. -/
def nonprojectiveTargetEquiv :
    {a : σ.IrreduciblePair //
      ¬ Projective (σ.obj a.1.2)} ≃
      σ.NonprojectiveTargetIrreduciblePair where
  toFun a := ⟨a.1.1, a.2, a.1.2⟩
  invFun a := ⟨⟨a.1, a.2.2⟩, a.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Reassociate the codomain of mesh rotation with irreducible occurrences
having noninjective source. -/
def noninjectiveSourceEquiv :
    σ.NoninjectiveSourceIrreduciblePair ≃
      {a : σ.IrreduciblePair //
        ¬ Injective (σ.obj a.1.1)} where
  toFun a := ⟨⟨a.1, a.2.2⟩, a.2.1⟩
  invFun a := ⟨a.1.1, a.2, a.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Mesh rotation as a finite partial translation on labelled arrow
occurrences. -/
def arrowOrbitData :
    QuotientSubmoduleEquidistribution.BoundaryTranslationChains.Data σ.IrreduciblePair
      (fun a ↦ Projective (σ.obj a.1.2))
      (fun a ↦ Injective (σ.obj a.1.1)) where
  tau := (nonprojectiveTargetEquiv σ).trans <|
    (M.arrowEquiv σ).trans (noninjectiveSourceEquiv σ)

omit [Fintype ι] [DecidableEq ι] in
/-- On endpoint pairs, the partial translation is the manuscript's
`(c → d) ↦ (τd → c)`. -/
theorem arrowOrbitData_tau_val
    (a : {a : σ.IrreduciblePair //
      ¬ Projective (σ.obj a.1.2)}) :
    ((arrowOrbitData σ M).tau a).1.1 =
      ((M.tau ⟨a.1.1.2, a.2⟩).1, a.1.1.1) :=
  rfl

omit [Fintype ι] [DecidableEq ι] in
/-- The inverse partial translation sends `(c → d)` with noninjective
source to `(d → τ⁻¹c)`. -/
theorem arrowOrbitData_tau_symm_val
    (a : {a : σ.IrreduciblePair //
      ¬ Injective (σ.obj a.1.1)}) :
    ((arrowOrbitData σ M).tau.symm a).1.1 =
      (a.1.1.2,
        (M.tau.symm ⟨a.1.1.1, a.2⟩).1) := by
  change
    ((M.arrowEquiv σ).symm
      ((noninjectiveSourceEquiv σ).symm a)).1 = _
  rfl

omit [DecidableEq ι] in
/-- Every arrow occurrence ending in a projective belongs to a finite
mesh-rotation chain ending at an occurrence starting in an injective. -/
theorem exists_iterate_arrowSuccessor_injectiveSource
    (a : σ.IrreduciblePair)
    (ha : Projective (σ.obj a.1.2)) :
    ∃ n ≤ Fintype.card σ.IrreduciblePair,
      Injective (σ.obj
        (((arrowOrbitData σ M).successor^[n] a).1.1)) :=
  (arrowOrbitData σ M).exists_iterate_mem_target a ha

/-- Length of the maximal mesh-rotation chain beginning at an occurrence
whose target is projective. -/
def arrowChainLength
    (a : σ.IrreduciblePair)
    (ha : Projective (σ.obj a.1.2)) : ℕ :=
  QuotientSubmoduleEquidistribution.BoundaryTranslationChains.Data.firstTargetIndex
    (arrowOrbitData σ M) a ha

/-- The occurrence at a specified position of a boundary-to-boundary arrow
chain. -/
def arrowChainAt
    (a : σ.IrreduciblePair)
    (n : ℕ) : σ.IrreduciblePair :=
  (arrowOrbitData σ M).successor^[n] a

omit [DecidableEq ι] in
/-- The last occurrence of the maximal chain starts at an injective
vertex. -/
theorem arrowChainAt_length_injectiveSource
    (a : σ.IrreduciblePair)
    (ha : Projective (σ.obj a.1.2)) :
    Injective (σ.obj
      ((M.arrowChainAt σ a (M.arrowChainLength σ a ha)).1.1)) :=
  QuotientSubmoduleEquidistribution.BoundaryTranslationChains.Data.firstTargetIndex_spec
    (arrowOrbitData σ M) a ha

omit [DecidableEq ι] in
/-- Starting at the injective-source endpoint and reversing mesh rotation
retraces the arrow chain at complementary positions. -/
theorem arrowChain_reverse_iterate_endpoint_eq
    (a : σ.IrreduciblePair)
    (ha : Projective (σ.obj a.1.2)) {n : ℕ}
    (hn : n ≤ M.arrowChainLength σ a ha) :
    (((M.arrowOrbitData σ).reverse.successor^[n])
        (M.arrowChainAt σ a (M.arrowChainLength σ a ha))) =
      M.arrowChainAt σ a (M.arrowChainLength σ a ha - n) := by
  exact (M.arrowOrbitData σ).reverse_iterate_targetEndpoint_eq a ha hn

omit [DecidableEq ι] in
/-- The reverse chain from the injective-source endpoint has the original
maximal arrow-chain length. -/
theorem arrowChain_reverseLength_endpoint_eq
    (a : σ.IrreduciblePair)
    (ha : Projective (σ.obj a.1.2)) :
    (M.arrowOrbitData σ).reverse.firstTargetIndex
        (M.arrowChainAt σ a (M.arrowChainLength σ a ha))
        (M.arrowChainAt_length_injectiveSource σ a ha) =
      M.arrowChainLength σ a ha := by
  exact (M.arrowOrbitData σ).reverse_firstTargetIndex_targetEndpoint a ha

omit [DecidableEq ι] in
/-- No earlier occurrence of the maximal chain starts at an injective. -/
theorem arrowChainAt_not_injectiveSource_of_lt
    (a : σ.IrreduciblePair)
    (ha : Projective (σ.obj a.1.2))
    {n : ℕ} (hn : n < M.arrowChainLength σ a ha) :
    ¬ Injective (σ.obj ((M.arrowChainAt σ a n).1.1)) :=
  QuotientSubmoduleEquidistribution.BoundaryTranslationChains.Data.not_mem_target_before_firstTargetIndex
      (arrowOrbitData σ M) a ha hn

omit [DecidableEq ι] in
/-- Occurrence labels at distinct positions of a maximal chain are
distinct, even when endpoint pairs elsewhere in the quiver coincide. -/
theorem arrowChainAt_ne_of_lt_le
    (a : σ.IrreduciblePair)
    (ha : Projective (σ.obj a.1.2))
    {i j : ℕ} (hij : i < j)
    (hj : j ≤ M.arrowChainLength σ a ha) :
    M.arrowChainAt σ a i ≠ M.arrowChainAt σ a j :=
  QuotientSubmoduleEquidistribution.BoundaryTranslationChains.Data.iterate_ne_of_lt_le_firstTargetIndex
      (arrowOrbitData σ M) a ha hij hj

omit [DecidableEq ι] in
/-- Before the terminal injective-source endpoint, the source of the next
arrow occurrence is the target of the current occurrence. -/
theorem arrowChainAt_succ_source_eq_target
    (a : σ.IrreduciblePair)
    (ha : Projective (σ.obj a.1.2))
    {n : ℕ} (hn : n < M.arrowChainLength σ a ha) :
    (M.arrowChainAt σ a (n + 1)).1.1 =
      (M.arrowChainAt σ a n).1.2 := by
  classical
  let x := M.arrowChainAt σ a n
  have hx : ¬ Injective (σ.obj x.1.1) :=
    M.arrowChainAt_not_injectiveSource_of_lt σ a ha hn
  have hsucc : M.arrowChainAt σ a (n + 1) =
      (M.arrowOrbitData σ).successor x := by
    simp only [ARMeshRotationData.arrowChainAt,
      Function.iterate_succ_apply', x]
  rw [hsucc]
  have hsuccessor : (M.arrowOrbitData σ).successor x =
      ((M.arrowOrbitData σ).tau.symm ⟨x, hx⟩).1 := by
    simp [QuotientSubmoduleEquidistribution.BoundaryTranslationChains.Data.successor, hx]
  rw [hsuccessor]
  have hrotate := M.arrowOrbitData_tau_symm_val σ ⟨x, hx⟩
  exact congrArg Prod.fst hrotate

omit [DecidableEq ι] in
/-- Before the terminal endpoint, the target of the next occurrence is
nonprojective. -/
theorem arrowChainAt_succ_target_nonprojective
    (a : σ.IrreduciblePair)
    (ha : Projective (σ.obj a.1.2))
    {n : ℕ} (hn : n < M.arrowChainLength σ a ha) :
    ¬ Projective (σ.obj (M.arrowChainAt σ a (n + 1)).1.2) := by
  let x := M.arrowChainAt σ a n
  have hx : ¬ Injective (σ.obj x.1.1) :=
    M.arrowChainAt_not_injectiveSource_of_lt σ a ha hn
  have hsucc : M.arrowChainAt σ a (n + 1) =
      (M.arrowOrbitData σ).successor x := by
    simp only [ARMeshRotationData.arrowChainAt,
      Function.iterate_succ_apply', x]
  rw [hsucc]
  exact (M.arrowOrbitData σ).successor_not_mem_source_of_not_mem_target hx

omit [DecidableEq ι] in
/-- Along an arrow chain, AR translation takes the target two vertex steps
ahead back to the current source. -/
theorem arTranslation_arrowChainAt_succ_target_eq_source
    (a : σ.IrreduciblePair)
    (ha : Projective (σ.obj a.1.2))
    {n : ℕ} (hn : n < M.arrowChainLength σ a ha) :
    (M.tau ⟨(M.arrowChainAt σ a (n + 1)).1.2,
        M.arrowChainAt_succ_target_nonprojective σ a ha hn⟩).1 =
      (M.arrowChainAt σ a n).1.1 := by
  let x := M.arrowChainAt σ a n
  let y := M.arrowChainAt σ a (n + 1)
  have hx : ¬ Injective (σ.obj x.1.1) :=
    M.arrowChainAt_not_injectiveSource_of_lt σ a ha hn
  have hy : ¬ Projective (σ.obj y.1.2) :=
    M.arrowChainAt_succ_target_nonprojective σ a ha hn
  have hsucc : y = (M.arrowOrbitData σ).successor x := by
    simp only [ARMeshRotationData.arrowChainAt,
      Function.iterate_succ_apply', x, y]
  have harg : (⟨y, hy⟩ : {q : σ.IrreduciblePair //
      ¬ Projective (σ.obj q.1.2)}) =
      ⟨(M.arrowOrbitData σ).successor x,
        (M.arrowOrbitData σ).successor_not_mem_source_of_not_mem_target hx⟩ := by
    apply Subtype.ext
    exact hsucc
  have hoccurrence :
      (M.arrowOrbitData σ).tau ⟨y, hy⟩ = ⟨x, hx⟩ := by
    rw [harg]
    exact (M.arrowOrbitData σ).tau_successor_of_not_mem_target hx
  have hrotate := M.arrowOrbitData_tau_val σ ⟨y, hy⟩
  calc
    (M.tau ⟨y.1.2, hy⟩).1 =
        (((M.arrowOrbitData σ).tau ⟨y, hy⟩).1.1).1 :=
      (congrArg Prod.fst hrotate).symm
    _ = x.1.1 := congrArg (fun q ↦ q.1.1.1) hoccurrence

/-- Vertex labels of an arrow chain, oriented from the projective-target
occurrence toward the injective-source occurrence.  The zeroth vertex is the
source of the starting arrow; every later vertex is the target of the
preceding occurrence. -/
def arrowChainVertexAt
    (a : σ.IrreduciblePair)
    (ha : Projective (σ.obj a.1.2))
    (e : Fin (M.arrowChainLength σ a ha + 2)) : ι :=
  if _he : e.1 = 0 then a.1.1
  else (M.arrowChainAt σ a (e.1 - 1)).1.2

/-- Regard an arrow-chain position as its source-vertex position. -/
def arrowChainPositionVertex
    (a : σ.IrreduciblePair)
    (ha : Projective (σ.obj a.1.2))
    (n : Fin (M.arrowChainLength σ a ha + 1)) :
    Fin (M.arrowChainLength σ a ha + 2) :=
  ⟨n.1, by omega⟩

/-- The target-vertex position immediately after an arrow-chain position. -/
def arrowChainPositionSuccVertex
    (a : σ.IrreduciblePair)
    (ha : Projective (σ.obj a.1.2))
    (n : Fin (M.arrowChainLength σ a ha + 1)) :
    Fin (M.arrowChainLength σ a ha + 2) :=
  ⟨n.1 + 1, by omega⟩

omit [DecidableEq ι] in
@[simp]
theorem arrowChainVertexAt_zero
    (a : σ.IrreduciblePair)
    (ha : Projective (σ.obj a.1.2)) :
    M.arrowChainVertexAt σ a ha ⟨0, by omega⟩ = a.1.1 := by
  simp [arrowChainVertexAt]

omit [DecidableEq ι] in
@[simp]
theorem arrowChainVertexAt_positionSucc
    (a : σ.IrreduciblePair)
    (ha : Projective (σ.obj a.1.2))
    (n : Fin (M.arrowChainLength σ a ha + 1)) :
    M.arrowChainVertexAt σ a ha
        (M.arrowChainPositionSuccVertex σ a ha n) =
      (M.arrowChainAt σ a n.1).1.2 := by
  simp [arrowChainVertexAt, arrowChainPositionSuccVertex]

omit [DecidableEq ι] in
/-- The source endpoint of an occurrence is the chain vertex at the same
position. -/
theorem arrowChainAt_source_eq_vertex
    (a : σ.IrreduciblePair)
    (ha : Projective (σ.obj a.1.2))
    (n : Fin (M.arrowChainLength σ a ha + 1)) :
    (M.arrowChainAt σ a n.1).1.1 =
      M.arrowChainVertexAt σ a ha
        (M.arrowChainPositionVertex σ a ha n) := by
  rcases n with ⟨_ | n, hn⟩
  · simp [arrowChainPositionVertex, arrowChainVertexAt,
      arrowChainAt]
  · have hnlt : n < M.arrowChainLength σ a ha := by omega
    rw [M.arrowChainAt_succ_source_eq_target σ a ha hnlt]
    simp [arrowChainVertexAt, arrowChainPositionVertex]

omit [DecidableEq ι] in
/-- Every occurrence is the arrow between its two consecutive chain
vertices. -/
theorem arrowChainAt_val_eq_vertices
    (a : σ.IrreduciblePair)
    (ha : Projective (σ.obj a.1.2))
    (n : Fin (M.arrowChainLength σ a ha + 1)) :
    (M.arrowChainAt σ a n.1).1 =
      (M.arrowChainVertexAt σ a ha
          (M.arrowChainPositionVertex σ a ha n),
        M.arrowChainVertexAt σ a ha
          (M.arrowChainPositionSuccVertex σ a ha n)) := by
  apply Prod.ext
  · exact M.arrowChainAt_source_eq_vertex σ a ha n
  · exact (M.arrowChainVertexAt_positionSucc σ a ha n).symm

omit [DecidableEq ι] in
/-- A chain vertex two steps ahead of a nonterminal occurrence is
nonprojective. -/
theorem arrowChainVertexAt_add_two_nonprojective
    (a : σ.IrreduciblePair)
    (ha : Projective (σ.obj a.1.2))
    {n : ℕ} (hn : n < M.arrowChainLength σ a ha) :
    ¬ Projective
      (σ.obj (M.arrowChainVertexAt σ a ha ⟨n + 2, by omega⟩)) := by
  let q : Fin (M.arrowChainLength σ a ha + 1) := ⟨n + 1, by omega⟩
  have hvertex := M.arrowChainVertexAt_positionSucc σ a ha q
  have hnp := M.arrowChainAt_succ_target_nonprojective σ a ha hn
  change ¬ Projective
    (σ.obj (M.arrowChainVertexAt σ a ha
      (M.arrowChainPositionSuccVertex σ a ha q)))
  rw [hvertex]
  simpa [q] using hnp

omit [DecidableEq ι] in
/-- AR translation moves two steps backward in the oriented chain-vertex
sequence. -/
theorem arTranslation_arrowChainVertexAt_add_two
    (a : σ.IrreduciblePair)
    (ha : Projective (σ.obj a.1.2))
    {n : ℕ} (hn : n < M.arrowChainLength σ a ha) :
    (M.tau ⟨M.arrowChainVertexAt σ a ha ⟨n + 2, by omega⟩,
        M.arrowChainVertexAt_add_two_nonprojective σ a ha hn⟩).1 =
      M.arrowChainVertexAt σ a ha ⟨n, by omega⟩ := by
  let q₀ : Fin (M.arrowChainLength σ a ha + 1) := ⟨n, by omega⟩
  let q₁ : Fin (M.arrowChainLength σ a ha + 1) := ⟨n + 1, by omega⟩
  have hsource := M.arrowChainAt_source_eq_vertex σ a ha q₀
  have htarget := M.arrowChainVertexAt_positionSucc σ a ha q₁
  have htranslate :=
    M.arTranslation_arrowChainAt_succ_target_eq_source σ a ha hn
  let v₂ : σ.NonprojectiveLabel :=
    ⟨M.arrowChainVertexAt σ a ha ⟨n + 2, by omega⟩,
      M.arrowChainVertexAt_add_two_nonprojective σ a ha hn⟩
  let t₂ : σ.NonprojectiveLabel :=
    ⟨(M.arrowChainAt σ a (n + 1)).1.2,
      M.arrowChainAt_succ_target_nonprojective σ a ha hn⟩
  have hv₂t₂ : v₂ = t₂ := by
    apply Subtype.ext
    change M.arrowChainVertexAt σ a ha
        (M.arrowChainPositionSuccVertex σ a ha q₁) =
      (M.arrowChainAt σ a (n + 1)).1.2
    exact htarget
  calc
    (M.tau v₂).1 = (M.tau t₂).1 := by rw [hv₂t₂]
    _ = (M.arrowChainAt σ a n).1.1 := by
      simpa [t₂] using htranslate
    _ = M.arrowChainVertexAt σ a ha ⟨n, by omega⟩ := by
      change (M.arrowChainAt σ a q₀.1).1.1 =
        M.arrowChainVertexAt σ a ha
          (M.arrowChainPositionVertex σ a ha q₀)
      exact hsource

end ARMeshRotationData

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
