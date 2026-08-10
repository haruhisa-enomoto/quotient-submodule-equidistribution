import OpConjecture.CategoryTheory.FiniteTauCategory
import OpConjecture.RepresentationDirected.IyamaWordMeshFiniteSkeleton
import OpConjecture.RepresentationDirected.IyamaWordMeshTauSequences

/-!
# The finite tau-category carried by the abstract word mesh

This file closes the singleton word-vertex tau-sequences under the displayed
finite matrix decomposition and packages the resulting chosen meshes.  It
also identifies their nonprojective and noninjective boundaries with previous
and next occurrences in the word.

No concrete algebra, quiver presentation, module enumeration, or
classification is used.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace OpConjecture.RepresentationDirected.IyamaMesh.WordMesh.FiniteTau

open OpConjecture.Iyama
open OpConjecture.RepresentationDirected.ARWord
open OpConjecture.RepresentationDirected.PrincipalPositivity
open OpConjecture.RepresentationDirected.IyamaMesh
open OpConjecture.RepresentationDirected.IyamaMesh.WordMesh
open OpConjecture.RepresentationDirected.IyamaMesh.WordMesh.AdditiveHull
open OpConjecture.RepresentationDirected.IyamaMesh.WordMeshRecurrence
open OpConjecture.RepresentationDirected.IyamaMesh.WordMeshStartingExactness
open OpConjecture.RepresentationDirected.IyamaMesh.WordMesh.RightRealization
open OpConjecture.RepresentationDirected.IyamaMesh.WordMesh.LeftRealization
open OpConjecture.RepresentationDirected.IyamaMesh.WordMesh.TauSequences

universe uK uL

variable {K : Type uK} [Field K]
variable {L : Type uL}

/-- The chosen right mesh of a finite matrix object is the componentwise
biproduct of the right meshes of its displayed word vertices. -/
def rightMesh
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    (X : AdditiveHull.Category (K := K) G Q hAlt) :
    ShortComplex (AdditiveHull.Category (K := K) G Q hAlt) :=
  shortComplexBiproduct fun i : X.ι ↦
    rightVertexMeshComplex (K := K) G Q hAlt (X.X i)

/-- The chosen left mesh of a finite matrix object is the componentwise
biproduct of the left meshes of its displayed word vertices. -/
def leftMesh
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    (X : AdditiveHull.Category (K := K) G Q hAlt) :
    ShortComplex (AdditiveHull.Category (K := K) G Q hAlt) :=
  shortComplexBiproduct fun i : X.ι ↦
    leftVertexMeshComplex (K := K) G Q hAlt (X.X i)

/-- The right endpoint of the componentwise chosen right mesh is the supplied
matrix object. -/
def rightTermIso
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    (X : AdditiveHull.Category (K := K) G Q hAlt) :
    (rightMesh (K := K) G Q hAlt X).X₃ ≅ X := by
  change (⨁ fun i : X.ι ↦
    (Mat_.embedding (WordMesh.Category (K := K) G Q hAlt)).obj (X.X i)) ≅ X
  exact (Mat_.isoBiproductEmbedding X).symm

/-- The left endpoint of the componentwise chosen left mesh is the supplied
matrix object. -/
def leftTermIso
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    (X : AdditiveHull.Category (K := K) G Q hAlt) :
    (leftMesh (K := K) G Q hAlt X).X₁ ≅ X := by
  change (⨁ fun i : X.ι ↦
    (Mat_.embedding (WordMesh.Category (K := K) G Q hAlt)).obj (X.X i)) ≅ X
  exact (Mat_.isoBiproductEmbedding X).symm

/-- The chosen componentwise right mesh is a right tau-sequence. -/
theorem rightTau
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    (weight : Fin Q.length → ℤ)
    (hweight : IsPositiveRightAdditive G Q weight)
    (X : AdditiveHull.Category (K := K) G Q hAlt) :
    RightTauSequence (rightMesh (K := K) G Q hAlt X) :=
  rightTauSequence_shortComplexBiproduct
    (nilpotentRadicalData (K := K) G Q hAlt)
    (fun i : X.ι ↦ rightVertexMeshComplex (K := K) G Q hAlt (X.X i))
    (fun i ↦ rightVertexTauSequence (K := K) G Q hAlt weight hweight (X.X i))

/-- The chosen componentwise left mesh is a left tau-sequence. -/
theorem leftTau
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    (weight : Fin Q.length → ℤ)
    (hweight : IsPositiveRightAdditive G Q weight)
    (X : AdditiveHull.Category (K := K) G Q hAlt) :
    LeftTauSequence (leftMesh (K := K) G Q hAlt X) :=
  leftTauSequence_shortComplexBiproduct
    (nilpotentRadicalData (K := K) G Q hAlt)
    (fun i : X.ι ↦ leftVertexMeshComplex (K := K) G Q hAlt (X.X i))
    (fun i ↦ leftVertexTauSequence (K := K) G Q hAlt weight hweight (X.X i))

/-- At a singleton vertex, the left term of the chosen right mesh is the
single external biproduct of its predecessor object. -/
def rightVertexLeftTermIso
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (x : Fin Q.length) :
    (rightMesh (K := K) G Q hAlt
      (AdditiveHull.vertexObj (K := K) G Q hAlt x)).X₁ ≅
        previousObj (K := K) G Q hAlt x := by
  change (⨁ fun _ : PUnit ↦ previousObj (K := K) G Q hAlt x) ≅
    previousObj (K := K) G Q hAlt x
  exact biproductUniqueIso _

/-- At a singleton vertex, the right term of the chosen left mesh is the
single external biproduct of its next-occurrence object. -/
def leftVertexRightTermIso
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (x : Fin Q.length) :
    (leftMesh (K := K) G Q hAlt
      (AdditiveHull.vertexObj (K := K) G Q hAlt x)).X₃ ≅
        nextObj (K := K) G Q hAlt x := by
  change (⨁ fun _ : PUnit ↦ nextObj (K := K) G Q hAlt x) ≅
    nextObj (K := K) G Q hAlt x
  exact biproductUniqueIso _

/-- The right mesh at a word vertex has zero left term exactly at a first
occurrence of its label. -/
theorem rightVertexLeftTerm_isZero_iff
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (x : Fin Q.length) :
    IsZero ((rightMesh (K := K) G Q hAlt
      (AdditiveHull.vertexObj (K := K) G Q hAlt x)).X₁) ↔
      ¬ Word.HasPrevious Q x := by
  constructor
  · intro hzero ⟨p, hp⟩
    let p₀ : (previousObj (K := K) G Q hAlt x).ι := ⟨p, hp⟩
    letI : Subsingleton (previousObj (K := K) G Q hAlt x).ι :=
      ⟨fun a b ↦ Subtype.ext (isPrevious_unique a.2 b.2)⟩
    have hprev : IsZero (previousObj (K := K) G Q hAlt x) :=
      hzero.of_iso (rightVertexLeftTermIso (K := K) G Q hAlt x).symm
    have hvertex : IsZero
        (AdditiveHull.vertexObj (K := K) G Q hAlt p) :=
      hprev.of_iso
        (entryIsoOfSubsingleton (K := K) G Q hAlt
          (previousObj (K := K) G Q hAlt x) p₀)
    exact (vertexObj_indec (K := K) G Q hAlt p).1 hvertex
  · intro hfirst
    have hprev := previousObj_isZero_of_first
      (K := K) G Q hAlt x hfirst
    exact hprev.of_iso (rightVertexLeftTermIso (K := K) G Q hAlt x)

/-- The left mesh at a word vertex has zero right term exactly at a last
occurrence of its label. -/
theorem leftVertexRightTerm_isZero_iff
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (x : Fin Q.length) :
    IsZero ((leftMesh (K := K) G Q hAlt
      (AdditiveHull.vertexObj (K := K) G Q hAlt x)).X₃) ↔
      ¬ Word.HasNext Q x := by
  constructor
  · intro hzero ⟨b, hb⟩
    let b₀ : (nextObj (K := K) G Q hAlt x).ι := ⟨b, hb⟩
    letI : Subsingleton (nextObj (K := K) G Q hAlt x).ι :=
      ⟨fun a c ↦ Subtype.ext (Word.isPrevious_target_unique a.2 c.2)⟩
    have hnext : IsZero (nextObj (K := K) G Q hAlt x) :=
      hzero.of_iso (leftVertexRightTermIso (K := K) G Q hAlt x).symm
    have hvertex : IsZero
        (AdditiveHull.vertexObj (K := K) G Q hAlt b) :=
      hnext.of_iso
        (entryIsoOfSubsingleton (K := K) G Q hAlt
          (nextObj (K := K) G Q hAlt x) b₀)
    exact (vertexObj_indec (K := K) G Q hAlt b).1 hvertex
  · intro hlast
    have hnext := nextObj_isZero_of_last
      (K := K) G Q hAlt x hlast
    exact hnext.of_iso (leftVertexRightTermIso (K := K) G Q hAlt x)

/-- Nonzero left terms of vertex right meshes are the nonprojective word
positions. -/
def rightBoundaryEquiv
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) :
    {x : Fin Q.length // ¬ IsZero ((rightMesh (K := K) G Q hAlt
      (AdditiveHull.vertexObj (K := K) G Q hAlt x)).X₁)} ≃
      {x : Fin Q.length // x ∉ Word.projectiveSet Q} where
  toFun x := ⟨x.1, by
    intro hx
    apply x.2
    exact (rightVertexLeftTerm_isZero_iff (K := K) G Q hAlt x.1).2 hx⟩
  invFun x := ⟨x.1, by
    intro hx
    apply x.2
    exact (rightVertexLeftTerm_isZero_iff (K := K) G Q hAlt x.1).1 hx⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Nonzero right terms of vertex left meshes are the noninjective word
positions. -/
def leftBoundaryEquiv
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) :
    {x : Fin Q.length // ¬ IsZero ((leftMesh (K := K) G Q hAlt
      (AdditiveHull.vertexObj (K := K) G Q hAlt x)).X₃)} ≃
      {x : Fin Q.length // x ∉ Word.injectiveSet Q} where
  toFun x := ⟨x.1, by
    intro hx
    apply x.2
    exact (leftVertexRightTerm_isZero_iff (K := K) G Q hAlt x.1).2 hx⟩
  invFun x := ⟨x.1, by
    intro hx
    apply x.2
    exact (leftVertexRightTerm_isZero_iff (K := K) G Q hAlt x.1).1 hx⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Previous and next occurrence give the partial translation equivalence for
the chosen categorical vertex meshes. -/
def tauPlusEquiv
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) :
    {x : Fin Q.length // ¬ IsZero ((rightMesh (K := K) G Q hAlt
      (AdditiveHull.vertexObj (K := K) G Q hAlt x)).X₁)} ≃
      {p : Fin Q.length // ¬ IsZero ((leftMesh (K := K) G Q hAlt
        (AdditiveHull.vertexObj (K := K) G Q hAlt p)).X₃)} :=
  (rightBoundaryEquiv (K := K) G Q hAlt).trans
    ((Word.tauEquiv Q).trans (leftBoundaryEquiv (K := K) G Q hAlt).symm)

/-! ## Rotation of one nonboundary mesh -/

/-- The permutation matrix which reindexes incoming middle vertices at `x`
as outgoing middle vertices at its predecessor `p`. -/
def middleRotationHom
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    {p x : Fin Q.length} (hpx : IsPrevious Q p x) :
    middleObj (K := K) G Q hAlt x ⟶
      outgoingMiddleObj (K := K) G Q hAlt p := by
  classical
  exact fun y z ↦ dite (z = middleRotationEquiv hAlt hpx y)
    (fun hz ↦ by
      subst z
      exact 𝟙 (WordMesh.obj (K := K) G Q hAlt y.1))
    (fun _ ↦ 0)

/-- The inverse permutation matrix to `middleRotationHom`. -/
def middleRotationInv
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    {p x : Fin Q.length} (hpx : IsPrevious Q p x) :
    outgoingMiddleObj (K := K) G Q hAlt p ⟶
      middleObj (K := K) G Q hAlt x := by
  classical
  exact fun z y ↦ dite (y = (middleRotationEquiv hAlt hpx).symm z)
    (fun hy ↦ by
      subst y
      exact 𝟙 (WordMesh.obj (K := K) G Q hAlt z.1))
    (fun _ ↦ 0)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Reindex the incoming middle object at `x` by the outgoing middle vertices
at its predecessor `p`. -/
def middleRotationIso
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    {p x : Fin Q.length} (hpx : IsPrevious Q p x) :
    middleObj (K := K) G Q hAlt x ≅
      outgoingMiddleObj (K := K) G Q hAlt p := by
  classical
  refine
    { hom := middleRotationHom (K := K) G Q hAlt hpx
      inv := middleRotationInv (K := K) G Q hAlt hpx
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply Mat_.hom_ext
    intro y y'
    rcases y with ⟨y, hy⟩
    rcases y' with ⟨y', hy'⟩
    let y₀ : (middleObj (K := K) G Q hAlt x).ι := ⟨y, hy⟩
    let y₁ : (middleObj (K := K) G Q hAlt x).ι := ⟨y', hy'⟩
    change (∑ z : {z : Fin Q.length // IsMiddle G Q p z},
      middleRotationHom (K := K) G Q hAlt hpx y₀ z ≫
        middleRotationInv (K := K) G Q hAlt hpx z y₁) =
      (𝟙 (middleObj (K := K) G Q hAlt x)) y₀ y₁
    simp only [middleRotationHom, middleRotationInv]
    rw [Finset.sum_eq_single (middleRotationEquiv hAlt hpx y₀)]
    · by_cases hval : y = y'
      · subst y'
        simp [y₀, y₁]
        change 𝟙 (WordMesh.obj (K := K) G Q hAlt y) ≫
          𝟙 (WordMesh.obj (K := K) G Q hAlt y) =
            𝟙 (WordMesh.obj (K := K) G Q hAlt y)
        simp
      · have hyy : y₀ ≠ y₁ := by
          intro h
          exact hval (congrArg Subtype.val h)
        have hrev : y₁ ≠ y₀ := Ne.symm hyy
        rw [Mat_.id_apply_of_ne _ _ _ hyy]
        simp [hrev]
    · intro z hz hzy
      simp [hzy]
    · intro hy
      exact (hy (Finset.mem_univ _)).elim
  · apply Mat_.hom_ext
    intro z z'
    rcases z with ⟨z, hz⟩
    rcases z' with ⟨z', hz'⟩
    let z₀ : (outgoingMiddleObj (K := K) G Q hAlt p).ι := ⟨z, hz⟩
    let z₁ : (outgoingMiddleObj (K := K) G Q hAlt p).ι := ⟨z', hz'⟩
    change (∑ y : {y : Fin Q.length // IsMiddle G Q y x},
      middleRotationInv (K := K) G Q hAlt hpx z₀ y ≫
        middleRotationHom (K := K) G Q hAlt hpx y z₁) =
      (𝟙 (outgoingMiddleObj (K := K) G Q hAlt p)) z₀ z₁
    simp only [middleRotationHom, middleRotationInv]
    rw [Finset.sum_eq_single ((middleRotationEquiv hAlt hpx).symm z₀)]
    · by_cases hval : z = z'
      · subst z'
        simp [z₀, z₁]
        change 𝟙 (WordMesh.obj (K := K) G Q hAlt z) ≫
          𝟙 (WordMesh.obj (K := K) G Q hAlt z) =
            𝟙 (WordMesh.obj (K := K) G Q hAlt z)
        simp
      · have hzz : z₀ ≠ z₁ := by
          intro h
          exact hval (congrArg Subtype.val h)
        have hrev : z₁ ≠ z₀ := Ne.symm hzz
        rw [Mat_.id_apply_of_ne _ _ _ hzz]
        simp [hrev]
    · intro y hy hyz
      simp [hyz]
    · intro hz
      exact (hz (Finset.mem_univ _)).elim

@[simp]
theorem middleRotationIso_hom_apply
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    {p x : Fin Q.length} (hpx : IsPrevious Q p x)
    (y : (middleObj (K := K) G Q hAlt x).ι) :
    (middleRotationIso (K := K) G Q hAlt hpx).hom y
        (middleRotationEquiv hAlt hpx y) =
      𝟙 (WordMesh.obj (K := K) G Q hAlt y.1) := by
  simp [middleRotationIso, middleRotationHom]

@[simp]
theorem middleRotationIso_hom_apply_of_ne
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    {p x : Fin Q.length} (hpx : IsPrevious Q p x)
    (y : (middleObj (K := K) G Q hAlt x).ι)
    (z : (outgoingMiddleObj (K := K) G Q hAlt p).ι)
    (hzy : z ≠ middleRotationEquiv hAlt hpx y) :
    (middleRotationIso (K := K) G Q hAlt hpx).hom y z = 0 := by
  simp [middleRotationIso, middleRotationHom, hzy]

/-- The unique predecessor summand is the singleton predecessor vertex. -/
def previousVertexIso
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    {p x : Fin Q.length} (hpx : IsPrevious Q p x) :
    previousObj (K := K) G Q hAlt x ≅
      AdditiveHull.vertexObj (K := K) G Q hAlt p := by
  let p₀ : (previousObj (K := K) G Q hAlt x).ι := ⟨p, hpx⟩
  letI : Subsingleton (previousObj (K := K) G Q hAlt x).ι :=
    ⟨fun a b ↦ Subtype.ext (isPrevious_unique a.2 b.2)⟩
  exact (entryIsoOfSubsingleton (K := K) G Q hAlt
    (previousObj (K := K) G Q hAlt x) p₀).symm

@[simp]
theorem previousVertexIso_hom_apply
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    {p x : Fin Q.length} (hpx : IsPrevious Q p x) :
    (previousVertexIso (K := K) G Q hAlt hpx).hom
        (⟨p, hpx⟩ : (previousObj (K := K) G Q hAlt x).ι) PUnit.unit =
      𝟙 (WordMesh.obj (K := K) G Q hAlt p) := by
  simp [previousVertexIso, entryIsoOfSubsingleton, entryProjection,
    previousObj]

/-- The unique next-occurrence summand is the singleton next vertex. -/
def nextVertexIso
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    {p x : Fin Q.length} (hpx : IsPrevious Q p x) :
    AdditiveHull.vertexObj (K := K) G Q hAlt x ≅
      nextObj (K := K) G Q hAlt p := by
  let x₀ : (nextObj (K := K) G Q hAlt p).ι := ⟨x, hpx⟩
  letI : Subsingleton (nextObj (K := K) G Q hAlt p).ι :=
    ⟨fun a b ↦ Subtype.ext (Word.isPrevious_target_unique a.2 b.2)⟩
  exact entryIsoOfSubsingleton (K := K) G Q hAlt
    (nextObj (K := K) G Q hAlt p) x₀

@[simp]
theorem nextVertexIso_hom_apply
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    {p x : Fin Q.length} (hpx : IsPrevious Q p x) :
    (nextVertexIso (K := K) G Q hAlt hpx).hom PUnit.unit
        (⟨x, hpx⟩ : (nextObj (K := K) G Q hAlt p).ι) =
      𝟙 (WordMesh.obj (K := K) G Q hAlt x) := by
  simp [nextVertexIso, entryIsoOfSubsingleton, entryInclusion, nextObj]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The right mesh ending at a repeated position is the left mesh beginning
at its predecessor. -/
def rightLeftVertexMeshIso
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    {p x : Fin Q.length} (hpx : IsPrevious Q p x) :
    rightVertexMeshComplex (K := K) G Q hAlt x ≅
      leftVertexMeshComplex (K := K) G Q hAlt p := by
  classical
  refine ShortComplex.isoMk
    (previousVertexIso (K := K) G Q hAlt hpx)
    (middleRotationIso (K := K) G Q hAlt hpx)
    (nextVertexIso (K := K) G Q hAlt hpx) ?_ ?_
  · apply Mat_.hom_ext
    intro q z
    rcases q with ⟨q, hqx⟩
    rcases z with ⟨z, hpz⟩
    have hq : q = p := isPrevious_unique hqx hpx
    subst q
    let q₀ : (previousObj (K := K) G Q hAlt x).ι := ⟨p, hpx⟩
    let z₀ : (outgoingMiddleObj (K := K) G Q hAlt p).ι := ⟨z, hpz⟩
    let r := middleRotationEquiv hAlt hpx
    change (∑ u : PUnit,
        (previousVertexIso (K := K) G Q hAlt hpx).hom
            q₀ u ≫
          quotientOutgoingMiddleArrow (K := K) G Q hAlt hpz) =
      ∑ y : {y : Fin Q.length // IsMiddle G Q y x},
        quotientPreviousMiddleArrow (K := K) G Q hAlt hpx y.2 ≫
          (middleRotationIso (K := K) G Q hAlt hpx).hom y z₀
    rw [Finset.univ_unique, Finset.sum_singleton]
    rw [Finset.sum_eq_single (r.symm z₀)]
    · have hm' : (middleRotationIso (K := K) G Q hAlt hpx).hom
          (r.symm z₀) z₀ = 𝟙 (WordMesh.obj (K := K) G Q hAlt z) := by
        change middleRotationHom (K := K) G Q hAlt hpx (r.symm z₀) z₀ = _
        simp [middleRotationHom, r]
        change 𝟙 (WordMesh.obj (K := K) G Q hAlt z) =
          𝟙 (WordMesh.obj (K := K) G Q hAlt z)
        rfl
      rw [previousVertexIso_hom_apply (K := K) G Q hAlt hpx, hm']
      change 𝟙 (WordMesh.obj (K := K) G Q hAlt p) ≫
          quotientOutgoingMiddleArrow (K := K) G Q hAlt hpz =
        quotientPreviousMiddleArrow (K := K) G Q hAlt hpx
            (r.symm z₀).2 ≫
          𝟙 (WordMesh.obj (K := K) G Q hAlt z)
      simp only [Category.id_comp]
      rfl
    · intro y hy hyne
      have hne : z₀ ≠ r y := by
        intro hzy
        apply hyne
        rw [hzy, r.symm_apply_apply]
      rw [middleRotationIso_hom_apply_of_ne
        (K := K) G Q hAlt hpx y z₀ hne]
      exact comp_zero
    · intro hy
      exact (hy (Finset.mem_univ _)).elim
  · apply Mat_.hom_ext
    intro y b
    rcases y with ⟨y, hyx⟩
    rcases b with ⟨b, hpb⟩
    have hb : b = x := Word.isPrevious_target_unique hpb hpx
    subst b
    let y₀ : (middleObj (K := K) G Q hAlt x).ι := ⟨y, hyx⟩
    let b₀ : (nextObj (K := K) G Q hAlt p).ι := ⟨x, hpx⟩
    let r := middleRotationEquiv hAlt hpx
    change (∑ z : {z : Fin Q.length // IsMiddle G Q p z},
        (middleRotationIso (K := K) G Q hAlt hpx).hom y₀ z ≫
          quotientMiddleNextArrow (K := K) G Q hAlt hpx z.2) =
      ∑ u : PUnit, quotientMiddleArrow (K := K) G Q hAlt hyx ≫
        (nextVertexIso (K := K) G Q hAlt hpx).hom u b₀
    conv_rhs => rw [Finset.univ_unique, Finset.sum_singleton]
    rw [Finset.sum_eq_single (r y₀)]
    · rw [middleRotationIso_hom_apply (K := K) G Q hAlt hpx y₀,
        nextVertexIso_hom_apply (K := K) G Q hAlt hpx]
      change 𝟙 (WordMesh.obj (K := K) G Q hAlt y) ≫
          quotientMiddleNextArrow (K := K) G Q hAlt hpx (r y₀).2 =
        quotientMiddleArrow (K := K) G Q hAlt hyx ≫
          𝟙 (WordMesh.obj (K := K) G Q hAlt x)
      simp only [Category.comp_id]
      rfl
    · intro z hz hzne
      rw [middleRotationIso_hom_apply_of_ne
        (K := K) G Q hAlt hpx y₀ z hzne]
      exact zero_comp
    · intro hz
      exact (hz (Finset.mem_univ _)).elim

/-! ## Componentwise rotation and the finite tau-category package -/

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Isomorphisms of a finite family of short complexes induce an isomorphism
of their componentwise biproducts. -/
def shortComplexBiproductIso
    {C : Type*} [CategoryTheory.Category C] [Preadditive C]
    [HasFiniteBiproducts C]
    {J : Type*} [Fintype J]
    (S T : J → ShortComplex C) (e : ∀ j, S j ≅ T j) :
    shortComplexBiproduct S ≅ shortComplexBiproduct T := by
  classical
  refine ShortComplex.isoMk
    (biproduct.mapIso fun j ↦ ShortComplex.π₁.mapIso (e j))
    (biproduct.mapIso fun j ↦ ShortComplex.π₂.mapIso (e j))
    (biproduct.mapIso fun j ↦ ShortComplex.π₃.mapIso (e j)) ?_ ?_
  · apply biproduct.hom_ext
    intro j
    change (biproduct.map (fun b ↦ (e b).hom.τ₁) ≫
        biproduct.map (fun b ↦ (T b).f)) ≫
          biproduct.π (fun b ↦ (T b).X₂) j =
      (biproduct.map (fun b ↦ (S b).f) ≫
        biproduct.map (fun b ↦ (e b).hom.τ₂)) ≫
          biproduct.π (fun b ↦ (T b).X₂) j
    calc
      _ = biproduct.π (fun b ↦ (S b).X₁) j ≫
          ((e j).hom.τ₁ ≫ (T j).f) := by
        simp only [Category.assoc, biproduct.map_π,
          biproduct.map_π_assoc]
      _ = biproduct.π (fun b ↦ (S b).X₁) j ≫
          ((S j).f ≫ (e j).hom.τ₂) := by rw [(e j).hom.comm₁₂]
      _ = _ := by simp only [Category.assoc, biproduct.map_π,
        biproduct.map_π_assoc]
  · apply biproduct.hom_ext
    intro j
    change (biproduct.map (fun b ↦ (e b).hom.τ₂) ≫
        biproduct.map (fun b ↦ (T b).g)) ≫
          biproduct.π (fun b ↦ (T b).X₃) j =
      (biproduct.map (fun b ↦ (S b).g) ≫
        biproduct.map (fun b ↦ (e b).hom.τ₃)) ≫
          biproduct.π (fun b ↦ (T b).X₃) j
    calc
      _ = biproduct.π (fun b ↦ (S b).X₂) j ≫
          ((e j).hom.τ₂ ≫ (T j).g) := by
        simp only [Category.assoc, biproduct.map_π,
          biproduct.map_π_assoc]
      _ = biproduct.π (fun b ↦ (S b).X₂) j ≫
          ((S j).g ≫ (e j).hom.τ₃) := by rw [(e j).hom.comm₂₃]
      _ = _ := by simp only [Category.assoc, biproduct.map_π,
        biproduct.map_π_assoc]

/-- The chosen componentwise right mesh of a repeated singleton vertex is
the chosen componentwise left mesh of its predecessor. -/
def rightLeftChosenVertexMeshIso
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    {p x : Fin Q.length} (hpx : IsPrevious Q p x) :
    rightMesh (K := K) G Q hAlt
        (AdditiveHull.vertexObj (K := K) G Q hAlt x) ≅
      leftMesh (K := K) G Q hAlt
        (AdditiveHull.vertexObj (K := K) G Q hAlt p) := by
  change shortComplexBiproduct
      (fun _ : PUnit ↦ rightVertexMeshComplex (K := K) G Q hAlt x) ≅
    shortComplexBiproduct
      (fun _ : PUnit ↦ leftVertexMeshComplex (K := K) G Q hAlt p)
  exact shortComplexBiproductIso _ _ fun _ ↦
    rightLeftVertexMeshIso (K := K) G Q hAlt hpx

/-- The categorical partial translation selects the literal predecessor of a
nonprojective word position. -/
theorem tauPlusEquiv_isPrevious
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    (X : {x : Fin Q.length // ¬ IsZero ((rightMesh (K := K) G Q hAlt
      (AdditiveHull.vertexObj (K := K) G Q hAlt x)).X₁)}) :
    IsPrevious Q (tauPlusEquiv (K := K) G Q hAlt X).1 X.1 := by
  change IsPrevious Q
    (Word.tauTo Q ((rightBoundaryEquiv (K := K) G Q hAlt) X)) X.1
  exact Word.tauTo_spec Q ((rightBoundaryEquiv (K := K) G Q hAlt) X)

/-- The chosen right and left meshes agree across categorical translation. -/
def rightLeftMeshIso
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    (X : {x : Fin Q.length // ¬ IsZero ((rightMesh (K := K) G Q hAlt
      (AdditiveHull.vertexObj (K := K) G Q hAlt x)).X₁)}) :
    rightMesh (K := K) G Q hAlt
        (AdditiveHull.vertexObj (K := K) G Q hAlt X.1) ≅
      leftMesh (K := K) G Q hAlt
        (AdditiveHull.vertexObj (K := K) G Q hAlt
          (tauPlusEquiv (K := K) G Q hAlt X).1) :=
  rightLeftChosenVertexMeshIso (K := K) G Q hAlt
    (tauPlusEquiv_isPrevious (K := K) G Q hAlt X)

/-- The finite tau-category carried by the abstract finite word-mesh additive
hull. -/
def finiteTauCategoryData
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    (weight : Fin Q.length → ℤ)
    (hweight : IsPositiveRightAdditive G Q weight) :
    FiniteTauCategoryData
      (AdditiveHull.Category (K := K) G Q hAlt) (Fin Q.length) where
  obj := AdditiveHull.vertexObj (K := K) G Q hAlt
  obj_indec := vertexObj_indec (K := K) G Q hAlt
  obj_end_local := fun _ ↦ inferInstance
  obj_decomposition := exists_iso_fin_biproduct_vertexObj (K := K) G Q hAlt
  obj_complete := obj_complete (K := K) G Q hAlt
  obj_skeletal := obj_skeletal (K := K) G Q hAlt
  radical := nilpotentRadicalData (K := K) G Q hAlt
  rightMesh := rightMesh (K := K) G Q hAlt
  leftMesh := leftMesh (K := K) G Q hAlt
  rightTermIso := rightTermIso (K := K) G Q hAlt
  leftTermIso := leftTermIso (K := K) G Q hAlt
  rightTau := rightTau (K := K) G Q hAlt weight hweight
  leftTau := leftTau (K := K) G Q hAlt weight hweight
  tauPlusEquiv := tauPlusEquiv (K := K) G Q hAlt
  rightLeftMeshIso := rightLeftMeshIso (K := K) G Q hAlt

end OpConjecture.RepresentationDirected.IyamaMesh.WordMesh.FiniteTau
