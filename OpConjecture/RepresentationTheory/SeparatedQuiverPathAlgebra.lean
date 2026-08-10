import OpConjecture.RepresentationTheory.SeparatedQuiverTriangularEquivalence
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# The path algebra of a separated quiver

Every path in a separated quiver is either a trivial vertex path or a single
arrow.  This file begins the explicit comparison between the corresponding
path-basis algebra and the triangular arrow-bimodule algebra.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped RightActions

namespace OpConjecture.SeparatedQuiverPathAlgebra

open OpConjecture.SeparatedQuiver
open OpConjecture.SeparatedQuiverArrowBimodule

universe uK uV v

variable (K : Type uK) (V : Type uV)
variable [Field K] [Fintype V] [DecidableEq V] [Quiver.{v} V]
variable [∀ i j : V, Fintype (i ⟶ j)] [∀ i j : V, DecidableEq (i ⟶ j)]

/-- The total type of original-quiver arrows. -/
abbrev ArrowIndex := Σ i j : V, (i ⟶ j)

/-- The basis labels of a separated path algebra: vertices and arrows. -/
abbrev BasisIndex := Vertex V ⊕ ArrowIndex V

/-- Classify a separated-quiver path as a vertex or as its unique arrow. -/
def classifyPath :
    OpConjecture.Foundation.Quiver.TotalPath (Vertex V) → BasisIndex V
  | ⟨a, _, .nil⟩ => Sum.inl a
  | ⟨Sum.inl _, Sum.inl _, .cons .nil e⟩ => PEmpty.elim e
  | ⟨Sum.inl i, Sum.inr j, .cons .nil e⟩ => Sum.inr ⟨i, j, e⟩
  | ⟨Sum.inr _, Sum.inl _, .cons .nil e⟩ => PEmpty.elim e
  | ⟨Sum.inr _, Sum.inr _, .cons .nil e⟩ => PEmpty.elim e
  | ⟨_, _, .cons (.cons _ f) e⟩ =>
      False.elim (no_composable_arrows f e)

/-- Reconstruct the path represented by a vertex-or-arrow basis label. -/
def pathOfBasisIndex :
    BasisIndex V → OpConjecture.Foundation.Quiver.TotalPath (Vertex V)
  | Sum.inl a => ⟨a, a, Quiver.Path.nil⟩
  | Sum.inr ⟨i, j, e⟩ =>
      ⟨Sum.inl i, Sum.inr j, Quiver.Hom.toPath e⟩

omit [Fintype V] [DecidableEq V] [∀ i j : V, Fintype (i ⟶ j)]
    [∀ i j : V, DecidableEq (i ⟶ j)] in
theorem pathOfBasisIndex_classifyPath
    (p : OpConjecture.Foundation.Quiver.TotalPath (Vertex V)) :
    pathOfBasisIndex V (classifyPath V p) = p := by
  obtain ⟨a, b, p⟩ := p
  cases p with
  | nil => rfl
  | @cons c _ p e =>
      cases p with
      | nil =>
          cases a with
          | inl i =>
              cases b with
              | inl j => exact PEmpty.elim e
              | inr j => rfl
          | inr i =>
              cases b with
              | inl j => exact PEmpty.elim e
              | inr j => exact PEmpty.elim e
      | @cons d _ p f => exact False.elim (no_composable_arrows f e)

omit [Fintype V] [DecidableEq V] [∀ i j : V, Fintype (i ⟶ j)]
    [∀ i j : V, DecidableEq (i ⟶ j)] in
theorem classifyPath_pathOfBasisIndex (x : BasisIndex V) :
    classifyPath V (pathOfBasisIndex V x) = x := by
  rcases x with a | ⟨i, j, e⟩
  · rfl
  · rfl

/-- The path basis of a separated quiver is canonically indexed by its
vertices and arrows. -/
def totalPathEquivBasisIndex :
    OpConjecture.Foundation.Quiver.TotalPath (Vertex V) ≃ BasisIndex V where
  toFun := classifyPath V
  invFun := pathOfBasisIndex V
  left_inv := pathOfBasisIndex_classifyPath V
  right_inv := classifyPath_pathOfBasisIndex V

/-- The triangular algebra attached to the separated quiver. -/
abbrev TriangularAlgebra :=
  SeparatedTriangularAlgebra.Algebra (V → K) (ArrowBimodule K V)

/-- Scalars enter both diagonal copies of the vertex ring. -/
def diagonalScalarHom : K →+* ((V → K) × (V → K)) where
  toFun k := ((fun _ ↦ k), (fun _ ↦ k))
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

/-- Field scalars act pointwise on the square-zero arrow ideal. -/
instance triangularIdealSMul :
    SMul K (SeparatedTriangularAlgebra.SeparatedIdeal (V → K)
      (ArrowBimodule K V)) where
  smul k a := ⟨k • a.val⟩

/-- The square-zero arrow ideal retains its ordinary pointwise
`K`-vector-space structure. -/
instance triangularIdealModule :
    Module K (SeparatedTriangularAlgebra.SeparatedIdeal (V → K)
      (ArrowBimodule K V)) :=
  Module.ofMinimalAxioms
    (by
      intro k a b
      apply SeparatedTriangularAlgebra.SeparatedIdeal.ext
      exact smul_add k a.val b.val)
    (by
      intro k l a
      apply SeparatedTriangularAlgebra.SeparatedIdeal.ext
      exact add_smul k l a.val)
    (by
      intro k l a
      apply SeparatedTriangularAlgebra.SeparatedIdeal.ext
      exact mul_smul k l a.val)
    (by
      intro a
      apply SeparatedTriangularAlgebra.SeparatedIdeal.ext
      exact one_smul K a.val)

omit [Fintype V] [DecidableEq V] [∀ i j : V, Fintype (i ⟶ j)]
    [∀ i j : V, DecidableEq (i ⟶ j)] in
@[simp]
theorem triangularIdeal_smul_val
    (k : K)
    (a : SeparatedTriangularAlgebra.SeparatedIdeal (V → K)
      (ArrowBimodule K V))
    (i j : V) (e : i ⟶ j) :
    (k • a).val i j e = k * a.val i j e := rfl

/-- Diagonal field scalars are compatible with the target-coordinate
action of the two-copy vertex ring. -/
instance triangularIdealLeftScalarTower :
    IsScalarTower K ((V → K) × (V → K))
      (SeparatedTriangularAlgebra.SeparatedIdeal (V → K)
        (ArrowBimodule K V)) where
  smul_assoc k s a := by
    apply SeparatedTriangularAlgebra.SeparatedIdeal.ext
    change (k • s).1 • a.val = k • (s.1 • a.val)
    change (k • s.1) • a.val = k • (s.1 • a.val)
    exact smul_assoc k s.1 a.val

/-- Diagonal field scalars are compatible with the source-coordinate
right action of the two-copy vertex ring. -/
instance triangularIdealRightScalarTower :
    IsScalarTower K ((V → K) × (V → K))ᵐᵒᵖ
      (SeparatedTriangularAlgebra.SeparatedIdeal (V → K)
        (ArrowBimodule K V)) where
  smul_assoc k s a := by
    apply SeparatedTriangularAlgebra.SeparatedIdeal.ext
    change a.val <• (MulOpposite.unop (k • s)).2 =
      k • (a.val <• (MulOpposite.unop s).2)
    change a.val <• (k • (MulOpposite.unop s).2) =
      k • (a.val <• (MulOpposite.unop s).2)
    funext i j e
    simp only [source_smul_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- The triangular arrow-bimodule algebra as a `K`-algebra, with scalars
embedded diagonally in its two vertex-ring copies. -/
instance triangularAlgebra : Algebra K (TriangularAlgebra K V) :=
  TrivSqZeroExt.algebra' K ((V → K) × (V → K))
    (SeparatedTriangularAlgebra.SeparatedIdeal (V → K)
      (ArrowBimodule K V))

omit [Fintype V] [DecidableEq V] [∀ i j : V, Fintype (i ⟶ j)]
    [∀ i j : V, DecidableEq (i ⟶ j)] in
@[simp]
theorem smul_radicalCoordinate_apply
    (k : K) (r : TriangularAlgebra K V) (i : V) :
    (k • r).fst.1 i = k * r.fst.1 i := rfl

omit [Fintype V] [DecidableEq V] [∀ i j : V, Fintype (i ⟶ j)]
    [∀ i j : V, DecidableEq (i ⟶ j)] in
@[simp]
theorem smul_topCoordinate_apply
    (k : K) (r : TriangularAlgebra K V) (i : V) :
    (k • r).fst.2 i = k * r.fst.2 i := rfl

omit [Fintype V] [DecidableEq V] [∀ i j : V, Fintype (i ⟶ j)]
    [∀ i j : V, DecidableEq (i ⟶ j)] in
@[simp]
theorem smul_arrowCoordinate_apply
    (k : K) (r : TriangularAlgebra K V)
    (i j : V) (e : i ⟶ j) :
    (k • r).snd.val i j e = k * r.snd.val i j e := rfl

omit [Fintype V] [DecidableEq V] [∀ i j : V, Fintype (i ⟶ j)]
    [∀ i j : V, DecidableEq (i ⟶ j)] in
@[simp]
theorem separatedIdeal_zero_val (i j : V) (e : i ⟶ j) :
    (0 : SeparatedTriangularAlgebra.SeparatedIdeal (V → K)
      (ArrowBimodule K V)).val i j e = 0 := rfl

/-- A separated vertex as its diagonal primitive idempotent in the
triangular algebra. -/
def vertexValue : Vertex V → TriangularAlgebra K V
  | Sum.inl i => SeparatedTriangularAlgebra.topScalar
      (PiRingModule.coordinateIdempotent K V i)
  | Sum.inr i => SeparatedTriangularAlgebra.radicalScalar
      (PiRingModule.coordinateIdempotent K V i)

/-- An original arrow as the corresponding square-zero basis vector in the
triangular algebra. -/
def arrowValue {i j : V} (e : i ⟶ j) : TriangularAlgebra K V :=
  TrivSqZeroExt.inr
    (⟨singleArrow K V e⟩ :
      SeparatedTriangularAlgebra.SeparatedIdeal (V → K)
        (ArrowBimodule K V))

/-- The triangular-algebra value of one vertex-or-arrow basis label. -/
def basisValue : BasisIndex V → TriangularAlgebra K V
  | Sum.inl a => vertexValue K V a
  | Sum.inr ⟨_, _, e⟩ => arrowValue K V e

/-- The triangular-algebra value of one separated-quiver path. -/
def pathValue (p : OpConjecture.Foundation.Quiver.TotalPath (Vertex V)) :
    TriangularAlgebra K V :=
  basisValue K V (classifyPath V p)

/-- Extend the path-basis values linearly to the separated path algebra. -/
def toTriangularLinear :
    OpConjecture.Foundation.pathAlgebra K (Vertex V) →ₗ[K] TriangularAlgebra K V :=
  Finsupp.linearCombination K (pathValue K V)

omit [Fintype V] [∀ i j : V, Fintype (i ⟶ j)] in
@[simp]
theorem toTriangularLinear_single
    (p : OpConjecture.Foundation.Quiver.TotalPath (Vertex V)) (k : K) :
    toTriangularLinear K V (OpConjecture.Foundation.PathAlgebra.single p k) =
      k • pathValue K V p := by
  exact Finsupp.linearCombination_single K k p

omit [Fintype V] [∀ i j : V, Fintype (i ⟶ j)] in
@[simp]
theorem toTriangularLinear_ofPath
    (p : OpConjecture.Foundation.Quiver.TotalPath (Vertex V)) :
    toTriangularLinear K V (OpConjecture.Foundation.PathAlgebra.ofPath p) =
      pathValue K V p := by
  rw [OpConjecture.Foundation.PathAlgebra.ofPath_eq_single, toTriangularLinear_single,
    one_smul]

/-- The trivial path at a plus vertex. -/
def plusVertexPath (i : V) : OpConjecture.Foundation.pathAlgebra K (Vertex V) :=
  OpConjecture.Foundation.PathAlgebra.vertexIdempotent K (Sum.inl i)

/-- The trivial path at a minus vertex. -/
def minusVertexPath (i : V) : OpConjecture.Foundation.pathAlgebra K (Vertex V) :=
  OpConjecture.Foundation.PathAlgebra.vertexIdempotent K (Sum.inr i)

/-- The separated length-one path attached to an original arrow. -/
def separatedArrowPath {i j : V} (e : i ⟶ j) :
    OpConjecture.Foundation.pathAlgebra K (Vertex V) :=
  OpConjecture.Foundation.PathAlgebra.ofArrow
    (show (Sum.inl i : Vertex V) ⟶ Sum.inr j from e)

/-- Reassemble a separated path-algebra element from the three triangular
coordinate families. -/
def fromTriangularLinear :
    TriangularAlgebra K V →ₗ[K] OpConjecture.Foundation.pathAlgebra K (Vertex V) where
  toFun r :=
    (∑ i : V, r.fst.2 i • plusVertexPath K V i) +
      (∑ i : V, r.fst.1 i • minusVertexPath K V i) +
        ∑ i : V, ∑ j : V, ∑ e : i ⟶ j,
          r.snd.val i j e • separatedArrowPath K V e
  map_add' r s := by
    change
      (∑ i : V, (r.fst.2 i + s.fst.2 i) • plusVertexPath K V i) +
          (∑ i : V, (r.fst.1 i + s.fst.1 i) • minusVertexPath K V i) +
            (∑ i : V, ∑ j : V, ∑ e : i ⟶ j,
              (r.snd.val i j e + s.snd.val i j e) •
                separatedArrowPath K V e) = _
    simp only [add_smul, Finset.sum_add_distrib]
    abel
  map_smul' k r := by
    change
      (∑ i : V, (k * r.fst.2 i) • plusVertexPath K V i) +
          (∑ i : V, (k * r.fst.1 i) • minusVertexPath K V i) +
            (∑ i : V, ∑ j : V, ∑ e : i ⟶ j,
              (k * r.snd.val i j e) • separatedArrowPath K V e) =
        k •
          ((∑ i : V, r.fst.2 i • plusVertexPath K V i) +
            (∑ i : V, r.fst.1 i • minusVertexPath K V i) +
              ∑ i : V, ∑ j : V, ∑ e : i ⟶ j,
                r.snd.val i j e • separatedArrowPath K V e)
    simp only [mul_smul, Finset.smul_sum, smul_add]

omit [Fintype V] [∀ i j : V, Fintype (i ⟶ j)] in
@[simp]
theorem toTriangularLinear_plusVertexPath (i : V) :
    toTriangularLinear K V (plusVertexPath K V i) =
      vertexValue K V (Sum.inl i) := by
  exact toTriangularLinear_ofPath K V
    ⟨Sum.inl i, Sum.inl i, Quiver.Path.nil⟩

omit [Fintype V] [∀ i j : V, Fintype (i ⟶ j)] in
@[simp]
theorem toTriangularLinear_minusVertexPath (i : V) :
    toTriangularLinear K V (minusVertexPath K V i) =
      vertexValue K V (Sum.inr i) := by
  exact toTriangularLinear_ofPath K V
    ⟨Sum.inr i, Sum.inr i, Quiver.Path.nil⟩

omit [Fintype V] [∀ i j : V, Fintype (i ⟶ j)] in
@[simp]
theorem toTriangularLinear_separatedArrowPath
    {i j : V} (e : i ⟶ j) :
    toTriangularLinear K V (separatedArrowPath K V e) =
      arrowValue K V e := by
  exact toTriangularLinear_ofPath K V
    ⟨Sum.inl i, Sum.inr j, Quiver.Hom.toPath e⟩

/-- Read one radical-diagonal coordinate. -/
def radicalCoordinate (i : V) : TriangularAlgebra K V →+ K where
  toFun r := r.fst.1 i
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Read one top-diagonal coordinate. -/
def topCoordinate (i : V) : TriangularAlgebra K V →+ K where
  toFun r := r.fst.2 i
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Read one square-zero arrow coordinate. -/
def arrowCoordinate (i j : V) (e : i ⟶ j) :
    TriangularAlgebra K V →+ K where
  toFun r := r.snd.val i j e
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Reading the path sums reconstructed from triangular coordinates recovers
those coordinates. -/
theorem toTriangularLinear_fromTriangularLinear
    (r : TriangularAlgebra K V) :
    toTriangularLinear K V (fromTriangularLinear K V r) = r := by
  change toTriangularLinear K V
      ((∑ i : V, r.fst.2 i • plusVertexPath K V i) +
        (∑ i : V, r.fst.1 i • minusVertexPath K V i) +
          ∑ i : V, ∑ j : V, ∑ e : i ⟶ j,
            r.snd.val i j e • separatedArrowPath K V e) = r
  simp only [map_add, map_sum, map_smul,
    toTriangularLinear_plusVertexPath,
    toTriangularLinear_minusVertexPath,
    toTriangularLinear_separatedArrowPath]
  apply Prod.ext
  · apply Prod.ext
    · funext i
      change radicalCoordinate K V i
          ((∑ x : V, r.fst.2 x • vertexValue K V (Sum.inl x)) +
            (∑ x : V, r.fst.1 x • vertexValue K V (Sum.inr x)) +
              ∑ x : V, ∑ y : V, ∑ f : x ⟶ y,
                r.snd.val x y f • arrowValue K V f) =
        radicalCoordinate K V i r
      rw [map_add, map_add, map_sum, map_sum, map_sum]
      simp [radicalCoordinate, vertexValue, arrowValue,
        SeparatedTriangularAlgebra.topScalar,
        SeparatedTriangularAlgebra.radicalScalar,
        PiRingModule.coordinateIdempotent, singleArrow]
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hb
        simp [hb.symm]
      · simp
    · funext i
      change topCoordinate K V i
          ((∑ x : V, r.fst.2 x • vertexValue K V (Sum.inl x)) +
            (∑ x : V, r.fst.1 x • vertexValue K V (Sum.inr x)) +
              ∑ x : V, ∑ y : V, ∑ f : x ⟶ y,
                r.snd.val x y f • arrowValue K V f) =
        topCoordinate K V i r
      rw [map_add, map_add, map_sum, map_sum, map_sum]
      simp [topCoordinate, vertexValue, arrowValue,
        SeparatedTriangularAlgebra.topScalar,
        SeparatedTriangularAlgebra.radicalScalar,
        PiRingModule.coordinateIdempotent, singleArrow]
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hb
        simp [hb.symm]
      · simp
  · apply SeparatedTriangularAlgebra.SeparatedIdeal.ext
    funext i j e
    change arrowCoordinate K V i j e
          ((∑ x : V, r.fst.2 x • vertexValue K V (Sum.inl x)) +
            (∑ x : V, r.fst.1 x • vertexValue K V (Sum.inr x)) +
              ∑ x : V, ∑ y : V, ∑ f : x ⟶ y,
                r.snd.val x y f • arrowValue K V f) =
        arrowCoordinate K V i j e r
    rw [map_add, map_add, map_sum, map_sum, map_sum]
    simp [arrowCoordinate, vertexValue, arrowValue,
      SeparatedTriangularAlgebra.topScalar,
      SeparatedTriangularAlgebra.radicalScalar,
      PiRingModule.coordinateIdempotent, singleArrow]
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single j]
      · rw [Finset.sum_eq_single e]
        · simp
        · intro f _ hf
          simp [hf]
        · simp
      · intro y _ hy
        simp [hy]
      · simp
    · intro x _ hx
      simp [hx]
    · simp

omit [∀ i j : V, DecidableEq (i ⟶ j)] in
@[simp]
theorem fromTriangularLinear_vertexValue_plus (i : V) :
    fromTriangularLinear K V (vertexValue K V (Sum.inl i)) =
      plusVertexPath K V i := by
  simp [fromTriangularLinear, vertexValue,
    SeparatedTriangularAlgebra.topScalar,
    PiRingModule.coordinateIdempotent]

omit [∀ i j : V, DecidableEq (i ⟶ j)] in
@[simp]
theorem fromTriangularLinear_vertexValue_minus (i : V) :
    fromTriangularLinear K V (vertexValue K V (Sum.inr i)) =
      minusVertexPath K V i := by
  simp [fromTriangularLinear, vertexValue,
    SeparatedTriangularAlgebra.radicalScalar,
    PiRingModule.coordinateIdempotent]

@[simp]
theorem fromTriangularLinear_arrowValue
    {i j : V} (e : i ⟶ j) :
    fromTriangularLinear K V (arrowValue K V e) =
      separatedArrowPath K V e := by
  simp [fromTriangularLinear, arrowValue, singleArrow]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · rw [Finset.sum_eq_single e]
      · simp
      · intro f _ hf
        simp [hf]
      · simp
    · intro y _ hy
      simp [hy]
    · simp
  · intro x _ hx
    simp [hx]
  · simp

/-- Reconstructing the triangular value of one separated path gives its
path-algebra basis element. -/
theorem fromTriangularLinear_pathValue
    (p : OpConjecture.Foundation.Quiver.TotalPath (Vertex V)) :
    fromTriangularLinear K V (pathValue K V p) =
      OpConjecture.Foundation.PathAlgebra.ofPath p := by
  obtain ⟨a, b, p⟩ := p
  cases p with
  | nil =>
      cases a with
      | inl i =>
          change fromTriangularLinear K V (vertexValue K V (Sum.inl i)) =
            plusVertexPath K V i
          exact fromTriangularLinear_vertexValue_plus K V i
      | inr i =>
          change fromTriangularLinear K V (vertexValue K V (Sum.inr i)) =
            minusVertexPath K V i
          exact fromTriangularLinear_vertexValue_minus K V i
  | @cons c _ p e =>
      cases p with
      | nil =>
          cases a with
          | inl i =>
              cases b with
              | inl j => exact PEmpty.elim e
              | inr j =>
                  change fromTriangularLinear K V (arrowValue K V e) =
                    separatedArrowPath K V e
                  exact fromTriangularLinear_arrowValue K V e
          | inr i =>
              cases b with
              | inl j => exact PEmpty.elim e
              | inr j => exact PEmpty.elim e
      | @cons d _ p f => exact False.elim (no_composable_arrows f e)

/-- The two coordinate maps are inverse on the whole separated path
algebra. -/
theorem fromTriangularLinear_toTriangularLinear
    (f : OpConjecture.Foundation.pathAlgebra K (Vertex V)) :
    fromTriangularLinear K V (toTriangularLinear K V f) = f := by
  induction f using OpConjecture.Foundation.PathAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, hf, hg]
  | single p k =>
      rw [toTriangularLinear_single, map_smul,
        fromTriangularLinear_pathValue,
        OpConjecture.Foundation.PathAlgebra.ofPath_eq_single,
        OpConjecture.Foundation.PathAlgebra.smul_single, mul_one]

/-- The separated path basis and the three triangular coordinate families
give a linear equivalence. -/
def linearEquiv :
    OpConjecture.Foundation.pathAlgebra K (Vertex V) ≃ₗ[K] TriangularAlgebra K V where
  toLinearMap := toTriangularLinear K V
  invFun := fromTriangularLinear K V
  left_inv := fromTriangularLinear_toTriangularLinear K V
  right_inv := toTriangularLinear_fromTriangularLinear K V

omit [Fintype V] [Quiver V] [∀ i j : V, Fintype (i ⟶ j)]
    [∀ i j : V, DecidableEq (i ⟶ j)] in
theorem coordinateIdempotent_mul (i j : V) :
    PiRingModule.coordinateIdempotent K V i *
        PiRingModule.coordinateIdempotent K V j =
      if i = j then PiRingModule.coordinateIdempotent K V i else 0 := by
  by_cases h : i = j
  · subst j
    simp [PiRingModule.coordinateIdempotent_mul_self]
  · simp [h, PiRingModule.coordinateIdempotent_mul_eq_zero]

omit [Fintype V] [DecidableEq V] [∀ i j : V, Fintype (i ⟶ j)]
    [∀ i j : V, DecidableEq (i ⟶ j)] in
@[simp]
theorem topScalar_zero :
    (SeparatedTriangularAlgebra.topScalar (0 : V → K) :
      TriangularAlgebra K V) = 0 := rfl

omit [Fintype V] [DecidableEq V] [∀ i j : V, Fintype (i ⟶ j)]
    [∀ i j : V, DecidableEq (i ⟶ j)] in
@[simp]
theorem radicalScalar_zero :
    (SeparatedTriangularAlgebra.radicalScalar (0 : V → K) :
      TriangularAlgebra K V) = 0 := rfl

omit [Fintype V] [∀ i j : V, Fintype (i ⟶ j)]
    [∀ i j : V, DecidableEq (i ⟶ j)] in
/-- Multiplication of diagonal vertex basis values. -/
theorem vertexValue_mul_vertexValue (a b : Vertex V) :
    vertexValue K V a * vertexValue K V b =
      if a = b then vertexValue K V a else 0 := by
  cases a with
  | inl i =>
      cases b with
      | inl j =>
          rw [show vertexValue K V (Sum.inl i) =
              SeparatedTriangularAlgebra.topScalar
                (PiRingModule.coordinateIdempotent K V i) by rfl,
            show vertexValue K V (Sum.inl j) =
              SeparatedTriangularAlgebra.topScalar
                (PiRingModule.coordinateIdempotent K V j) by rfl,
            ← SeparatedTriangularAlgebra.topScalar_mul,
            coordinateIdempotent_mul]
          by_cases h : i = j <;> simp [h]
      | inr j =>
          change SeparatedTriangularAlgebra.topScalar
              (PiRingModule.coordinateIdempotent K V i) *
            SeparatedTriangularAlgebra.radicalScalar
              (PiRingModule.coordinateIdempotent K V j) = 0
          change TrivSqZeroExt.inl
              ((0, PiRingModule.coordinateIdempotent K V i) :
                (V → K) × (V → K)) *
            TrivSqZeroExt.inl
              ((PiRingModule.coordinateIdempotent K V j, 0) :
                (V → K) × (V → K)) = 0
          rw [TrivSqZeroExt.inl_mul_inl]
          congr 1
          ext <;> simp
  | inr i =>
      cases b with
      | inl j =>
          change SeparatedTriangularAlgebra.radicalScalar
              (PiRingModule.coordinateIdempotent K V i) *
            SeparatedTriangularAlgebra.topScalar
              (PiRingModule.coordinateIdempotent K V j) = 0
          change TrivSqZeroExt.inl
              ((PiRingModule.coordinateIdempotent K V i, 0) :
                (V → K) × (V → K)) *
            TrivSqZeroExt.inl
              ((0, PiRingModule.coordinateIdempotent K V j) :
                (V → K) × (V → K)) = 0
          rw [TrivSqZeroExt.inl_mul_inl]
          congr 1
          ext <;> simp
      | inr j =>
          rw [show vertexValue K V (Sum.inr i) =
              SeparatedTriangularAlgebra.radicalScalar
                (PiRingModule.coordinateIdempotent K V i) by rfl,
            show vertexValue K V (Sum.inr j) =
              SeparatedTriangularAlgebra.radicalScalar
                (PiRingModule.coordinateIdempotent K V j) by rfl,
            ← SeparatedTriangularAlgebra.radicalScalar_mul,
            coordinateIdempotent_mul]
          by_cases h : i = j <;> simp [h]

omit [Fintype V] [∀ i j : V, Fintype (i ⟶ j)] in
/-- A vertex basis value acts on an arrow basis value through the arrow's
target vertex. -/
theorem vertexValue_mul_arrowValue
    (a : Vertex V) {i j : V} (e : i ⟶ j) :
    vertexValue K V a * arrowValue K V e =
      if a = Sum.inr j then arrowValue K V e else 0 := by
  cases a with
  | inl k =>
      change TrivSqZeroExt.inl
          ((0, PiRingModule.coordinateIdempotent K V k) :
            (V → K) × (V → K)) *
        TrivSqZeroExt.inr
          (⟨singleArrow K V e⟩ :
            SeparatedTriangularAlgebra.SeparatedIdeal (V → K)
              (ArrowBimodule K V)) = (0 : TriangularAlgebra K V)
      rw [TrivSqZeroExt.inl_mul_inr]
      congr 1
      apply SeparatedTriangularAlgebra.SeparatedIdeal.ext
      change (0 : V → K) • singleArrow K V e = 0
      funext i' j' e'
      simp
  | inr k =>
      change SeparatedTriangularAlgebra.radicalScalar
          (PiRingModule.coordinateIdempotent K V k) *
        TrivSqZeroExt.inr
          (⟨singleArrow K V e⟩ :
            SeparatedTriangularAlgebra.SeparatedIdeal (V → K)
              (ArrowBimodule K V)) = _
      rw [SeparatedTriangularAlgebra.radicalScalar_mul_inr]
      by_cases h : k = j
      · subst k
        rw [coordinateIdempotent_target_smul_singleArrow]
        rw [if_pos rfl]
        rfl
      · rw [coordinateIdempotent_target_smul_singleArrow_eq_zero K V e h]
        rw [show (⟨(0 : ArrowBimodule K V)⟩ :
            SeparatedTriangularAlgebra.SeparatedIdeal (V → K)
              (ArrowBimodule K V)) = 0 by rfl,
          TrivSqZeroExt.inr_zero]
        simp [h]

omit [Fintype V] [∀ i j : V, Fintype (i ⟶ j)] in
/-- An arrow basis value acts on a vertex basis value through the arrow's
source vertex. -/
theorem arrowValue_mul_vertexValue
    {i j : V} (e : i ⟶ j) (a : Vertex V) :
    arrowValue K V e * vertexValue K V a =
      if a = Sum.inl i then arrowValue K V e else 0 := by
  cases a with
  | inl k =>
      rw [show vertexValue K V (Sum.inl k) =
          SeparatedTriangularAlgebra.topScalar
            (PiRingModule.coordinateIdempotent K V k) by rfl,
        show arrowValue K V e = TrivSqZeroExt.inr
          (⟨singleArrow K V e⟩ :
            SeparatedTriangularAlgebra.SeparatedIdeal (V → K)
              (ArrowBimodule K V)) by rfl,
        SeparatedTriangularAlgebra.inr_mul_topScalar]
      by_cases h : k = i
      · subst k
        simp
      · rw [singleArrow_source_smul_coordinateIdempotent_eq_zero K V e h]
        rw [show (⟨(0 : ArrowBimodule K V)⟩ :
            SeparatedTriangularAlgebra.SeparatedIdeal (V → K)
              (ArrowBimodule K V)) = 0 by rfl,
          TrivSqZeroExt.inr_zero]
        simp [h]
  | inr k =>
      change TrivSqZeroExt.inr
          (⟨singleArrow K V e⟩ :
            SeparatedTriangularAlgebra.SeparatedIdeal (V → K)
              (ArrowBimodule K V)) *
        TrivSqZeroExt.inl
          ((PiRingModule.coordinateIdempotent K V k, 0) :
            (V → K) × (V → K)) = 0
      rw [TrivSqZeroExt.inr_mul_inl]
      congr 1
      apply SeparatedTriangularAlgebra.SeparatedIdeal.ext
      change singleArrow K V e <• (0 : V → K) = 0
      simp

omit [Fintype V] [∀ i j : V, Fintype (i ⟶ j)] in
@[simp]
theorem arrowValue_mul_arrowValue
    {i j k l : V} (e : i ⟶ j) (f : k ⟶ l) :
    arrowValue K V e * arrowValue K V f = 0 := by
  simp [arrowValue, TrivSqZeroExt.inr_mul_inr]

omit [Fintype V] [∀ i j : V, Fintype (i ⟶ j)] in
@[simp]
theorem pathValue_pathOfBasisIndex (b : BasisIndex V) :
    pathValue K V (pathOfBasisIndex V b) = basisValue K V b := by
  rw [pathValue, classifyPath_pathOfBasisIndex]

omit [Fintype V] [∀ i j : V, Fintype (i ⟶ j)] in
/-- The path-basis assignment respects the partial concatenation of paths. -/
theorem pathValue_mul_pathValue
    (x y : OpConjecture.Foundation.Quiver.TotalPath (Vertex V)) :
    pathValue K V x * pathValue K V y =
      (x.mul? y).elim 0 (pathValue K V) := by
  rw [← pathOfBasisIndex_classifyPath V x,
    ← pathOfBasisIndex_classifyPath V y]
  generalize hx : classifyPath V x = bx
  generalize hy : classifyPath V y = cy
  rcases bx with a | ⟨i, j, e⟩
  · rcases cy with b | ⟨k, l, f⟩
    · simp only [pathValue_pathOfBasisIndex, basisValue]
      rw [vertexValue_mul_vertexValue]
      by_cases h : a = b
      · subst b
        rw [if_pos rfl]
        change vertexValue K V a =
          (OpConjecture.Foundation.Quiver.TotalPath.mul?
            (⟨a, a, Quiver.Path.nil⟩ :
              OpConjecture.Foundation.Quiver.TotalPath (Vertex V))
            ⟨a, a, Quiver.Path.nil⟩).elim 0 (pathValue K V)
        rw [OpConjecture.Foundation.Quiver.TotalPath.mul?_mk,
          _root_.Quiver.Path.comp_nil]
        rfl
      · rw [if_neg h,
          OpConjecture.Foundation.Quiver.TotalPath.mul?_eq_none (fun hba => h hba.symm)]
        rfl
    · simp only [pathValue_pathOfBasisIndex, basisValue]
      rw [vertexValue_mul_arrowValue]
      by_cases h : a = Sum.inr l
      · subst a
        rw [if_pos rfl]
        change arrowValue K V f =
          (OpConjecture.Foundation.Quiver.TotalPath.mul?
            (⟨Sum.inr l, Sum.inr l, Quiver.Path.nil⟩ :
              OpConjecture.Foundation.Quiver.TotalPath (Vertex V))
            ⟨Sum.inl k, Sum.inr l, Quiver.Hom.toPath f⟩).elim
              0 (pathValue K V)
        rw [OpConjecture.Foundation.Quiver.TotalPath.mul?_mk,
          _root_.Quiver.Path.comp_nil]
        rfl
      · rw [if_neg h,
          OpConjecture.Foundation.Quiver.TotalPath.mul?_eq_none (fun hla => h hla.symm)]
        rfl
  · rcases cy with b | ⟨k, l, f⟩
    · simp only [pathValue_pathOfBasisIndex, basisValue]
      rw [arrowValue_mul_vertexValue]
      by_cases h : b = Sum.inl i
      · subst b
        rw [if_pos rfl]
        change arrowValue K V e =
          (OpConjecture.Foundation.Quiver.TotalPath.mul?
            (⟨Sum.inl i, Sum.inr j, Quiver.Hom.toPath e⟩ :
              OpConjecture.Foundation.Quiver.TotalPath (Vertex V))
            ⟨Sum.inl i, Sum.inl i, Quiver.Path.nil⟩).elim
              0 (pathValue K V)
        rw [OpConjecture.Foundation.Quiver.TotalPath.mul?_mk,
          _root_.Quiver.Path.nil_comp]
        rfl
      · rw [if_neg h, OpConjecture.Foundation.Quiver.TotalPath.mul?_eq_none h]
        rfl
    · simp only [pathValue_pathOfBasisIndex, basisValue]
      rw [arrowValue_mul_arrowValue,
        OpConjecture.Foundation.Quiver.TotalPath.mul?_eq_none (by
          change (Sum.inr l : Vertex V) ≠ Sum.inl i
          simp)]
      rfl

omit [Fintype V] [DecidableEq V] [∀ i j : V, Fintype (i ⟶ j)]
    [∀ i j : V, DecidableEq (i ⟶ j)] in
/-- Pulling scalar coefficients out of both factors multiplies them. -/
theorem smul_mul_smul (a b : K) (r s : TriangularAlgebra K V) :
    (a • r) * (b • s) = (a * b) • (r * s) := by
  calc
    (a • r) * (b • s) = a • (r * (b • s)) :=
      Algebra.smul_mul_assoc a r (b • s)
    _ = a • (b • (r * s)) :=
      congrArg (a • ·) (Algebra.mul_smul_comm b r s)
    _ = (a * b) • (r * s) := smul_smul a b (r * s)

omit [Fintype V] [∀ i j : V, Fintype (i ⟶ j)] in
/-- The linear comparison respects products of coefficient-weighted basis
paths. -/
theorem toTriangularLinear_single_mul_single
    (x y : OpConjecture.Foundation.Quiver.TotalPath (Vertex V)) (a b : K) :
    toTriangularLinear K V
        (OpConjecture.Foundation.PathAlgebra.single x a *
          OpConjecture.Foundation.PathAlgebra.single y b) =
      toTriangularLinear K V (OpConjecture.Foundation.PathAlgebra.single x a) *
        toTriangularLinear K V (OpConjecture.Foundation.PathAlgebra.single y b) := by
  rw [OpConjecture.Foundation.PathAlgebra.single_mul_single]
  cases hxy : x.mul? y with
  | none =>
      simp only [Option.elim_none, map_zero, toTriangularLinear_single]
      rw [smul_mul_smul, pathValue_mul_pathValue, hxy,
        Option.elim_none, smul_zero]
  | some z =>
      simp only [Option.elim_some, toTriangularLinear_single]
      rw [smul_mul_smul, pathValue_mul_pathValue, hxy,
        Option.elim_some]

omit [∀ i j : V, Fintype (i ⟶ j)] in
/-- The linear comparison is multiplicative on arbitrary path-algebra
elements. -/
theorem toTriangularLinear_mul
    (f g : OpConjecture.Foundation.pathAlgebra K (Vertex V)) :
    toTriangularLinear K V (f * g) =
      toTriangularLinear K V f * toTriangularLinear K V g := by
  induction f using OpConjecture.Foundation.PathAlgebra.induction_linear with
  | zero => simp
  | add f₁ f₂ hf₁ hf₂ =>
      rw [add_mul, map_add, map_add, hf₁, hf₂, add_mul]
  | single x a =>
      induction g using OpConjecture.Foundation.PathAlgebra.induction_linear with
      | zero => simp
      | add g₁ g₂ hg₁ hg₂ =>
          rw [mul_add, map_add, map_add, hg₁, hg₂, mul_add]
      | single y b =>
          exact toTriangularLinear_single_mul_single K V x y a b

/-- Multiplicativity plus bijectivity forces the linear comparison to
preserve the identity. -/
theorem toTriangularLinear_one :
    toTriangularLinear K V (1 : OpConjecture.Foundation.pathAlgebra K (Vertex V)) = 1 := by
  let x : OpConjecture.Foundation.pathAlgebra K (Vertex V) :=
    (linearEquiv K V).symm (1 : TriangularAlgebra K V)
  calc
    toTriangularLinear K V (1 : OpConjecture.Foundation.pathAlgebra K (Vertex V)) =
        toTriangularLinear K V 1 * 1 := (mul_one _).symm
    _ = toTriangularLinear K V 1 * toTriangularLinear K V x := by
      rw [show toTriangularLinear K V x = 1 by
        exact (linearEquiv K V).apply_symm_apply 1]
    _ = toTriangularLinear K V (1 * x) :=
      (toTriangularLinear_mul K V 1 x).symm
    _ = toTriangularLinear K V x := by rw [one_mul]
    _ = 1 := (linearEquiv K V).apply_symm_apply 1

/-- The literal path algebra of the separated quiver is the triangular
arrow-bimodule algebra. -/
def algebraEquiv :
    OpConjecture.Foundation.pathAlgebra K (Vertex V) ≃ₐ[K] TriangularAlgebra K V :=
  AlgEquiv.ofLinearEquiv (linearEquiv K V)
    (toTriangularLinear_one K V) (toTriangularLinear_mul K V)

/-- Literal separated-quiver representations are modules over the literal
project-foundation path algebra of the separated quiver. -/
def moduleEquivalence :
    CategoryTheory.Equivalence
      (OpConjecture.Foundation.QuiverRep K (Vertex V))
      (ModuleCat.{uV} (OpConjecture.Foundation.pathAlgebra K (Vertex V))) :=
  (SeparatedQuiverTriangularEquivalence.moduleEquivalence K V).trans
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
      (algebraEquiv K V).toRingEquiv)

end OpConjecture.SeparatedQuiverPathAlgebra
