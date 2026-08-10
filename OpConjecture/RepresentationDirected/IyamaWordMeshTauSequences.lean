import OpConjecture.CategoryTheory.MatWeakExactness
import OpConjecture.RepresentationDirected.IyamaMeshStrictness
import OpConjecture.RepresentationDirected.IyamaWordMeshLeftRealization
import OpConjecture.RepresentationDirected.IyamaWordMeshRadical

/-!
# Tau-sequences in the finite word-mesh additive hull

This file turns the incoming and outgoing representable exactness of the
abstract word-mesh quotient into genuine weak kernels and weak cokernels in
its finite matrix additive hull.  It then supplies the radical approximation
and minimality arguments needed for the vertex right and left tau-sequences.

No concrete algebra, quiver presentation, module enumeration, or
classification is used.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open CategoryTheory CategoryTheory.Limits

namespace OpConjecture.RepresentationDirected.IyamaMesh.WordMesh.TauSequences

open OpConjecture.Iyama
open OpConjecture.CategoricalRadical
open OpConjecture.RepresentationDirected.ARWord
open OpConjecture.RepresentationDirected.PrincipalPositivity
open OpConjecture.RepresentationDirected.IyamaMesh.WordMesh
open OpConjecture.RepresentationDirected.IyamaMesh.WordMesh.AdditiveHull
open OpConjecture.RepresentationDirected.IyamaMesh.WordMeshRecurrence
open OpConjecture.RepresentationDirected.IyamaMesh.WordMeshStartingExactness
open OpConjecture.RepresentationDirected.IyamaMesh.WordMesh.RightRealization
open OpConjecture.RepresentationDirected.IyamaMesh.WordMesh.LeftRealization

universe uK uL

variable {K : Type uK} [Field K]
variable {L : Type uL}

/-! ## Vertex mesh complexes -/

/-- The right mesh ending at a singleton word vertex. -/
def rightVertexMeshComplex
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (x : Fin Q.length) :
    ShortComplex (AdditiveHull.Category (K := K) G Q hAlt) :=
  ShortComplex.mk
    (previousToMiddle (K := K) G Q hAlt x)
    (middleToVertex (K := K) G Q hAlt x)
    (by
      apply Mat_.hom_ext
      intro p z
      cases z
      change {p : Fin Q.length // IsPrevious Q p x} at p
      change (∑ y,
        quotientPreviousMiddleArrow (K := K) G Q hAlt p.2 y.2 ≫
          quotientMiddleArrow (K := K) G Q hAlt y.2) = 0
      calc
        _ = ∑ y : {y : Fin Q.length // IsMiddle G Q y x},
            WordMesh.quotientHom (K := K) G Q hAlt
            (pathPreviousMiddleArrow (K := K) G Q hAlt p.2 y.2 ≫
              WordPath.middleArrow (K := K) G Q y.2) := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [WordMesh.quotientHom_comp]
          rfl
        _ = WordMesh.quotientHom (K := K) G Q hAlt
            (WordPath.meshRelation (K := K) G Q hAlt p.2) := by
          rw [WordPath.meshRelation]
          change (∑ y : {y : Fin Q.length // IsMiddle G Q y x},
              (WordMesh.quotientHomLinearMap
            (K := K) G Q hAlt p.1 x)
              (pathPreviousMiddleArrow (K := K) G Q hAlt p.2 y.2 ≫
                WordPath.middleArrow (K := K) G Q y.2)) =
            (WordMesh.quotientHomLinearMap (K := K) G Q hAlt p.1 x)
              (∑ y : {y : Fin Q.length // IsMiddle G Q y x},
                pathPreviousMiddleArrow (K := K) G Q hAlt p.2 y.2 ≫
                  WordPath.middleArrow (K := K) G Q y.2)
          rw [map_sum]
        _ = 0 := WordMesh.quotientHom_meshRelation_eq_zero
          (K := K) G Q hAlt p.2)

/-- The left mesh starting at a singleton word vertex. -/
def leftVertexMeshComplex
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (x : Fin Q.length) :
    ShortComplex (AdditiveHull.Category (K := K) G Q hAlt) :=
  ShortComplex.mk
    (vertexToOutgoingMiddle (K := K) G Q hAlt x)
    (outgoingMiddleToNext (K := K) G Q hAlt x)
    (by
      apply Mat_.hom_ext
      intro z b
      cases z
      change {b : Fin Q.length // IsPrevious Q x b} at b
      change (∑ y,
        quotientOutgoingMiddleArrow (K := K) G Q hAlt y.2 ≫
          quotientMiddleNextArrow (K := K) G Q hAlt b.2 y.2) = 0
      calc
        _ = ∑ y : {y : Fin Q.length // IsMiddle G Q x y},
            WordMesh.quotientHom (K := K) G Q hAlt
            (WordPath.middleArrow (K := K) G Q y.2 ≫
              pathMiddleNextArrow (K := K) G Q hAlt b.2 y.2) := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [WordMesh.quotientHom_comp]
          rfl
        _ = WordMesh.quotientHom (K := K) G Q hAlt
            (∑ y : {y : Fin Q.length // IsMiddle G Q x y},
              WordPath.middleArrow (K := K) G Q y.2 ≫
              pathMiddleNextArrow (K := K) G Q hAlt b.2 y.2) := by
          change (∑ y : {y : Fin Q.length // IsMiddle G Q x y},
              (WordMesh.quotientHomLinearMap
            (K := K) G Q hAlt x b.1)
              (WordPath.middleArrow (K := K) G Q y.2 ≫
                pathMiddleNextArrow (K := K) G Q hAlt b.2 y.2)) =
            (WordMesh.quotientHomLinearMap (K := K) G Q hAlt x b.1)
              (∑ y : {y : Fin Q.length // IsMiddle G Q x y},
                WordPath.middleArrow (K := K) G Q y.2 ≫
                  pathMiddleNextArrow (K := K) G Q hAlt b.2 y.2)
          rw [map_sum]
        _ = WordMesh.quotientHom (K := K) G Q hAlt
            (WordPath.meshRelation (K := K) G Q hAlt b.2) := by
          rw [meshRelation_eq_sum_outgoing (K := K) G Q hAlt b.2]
        _ = 0 := WordMesh.quotientHom_meshRelation_eq_zero
          (K := K) G Q hAlt b.2)

@[simp]
theorem rightVertexMeshComplex_X₁
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (x : Fin Q.length) :
    (rightVertexMeshComplex (K := K) G Q hAlt x).X₁ =
      previousObj (K := K) G Q hAlt x :=
  rfl

@[simp]
theorem rightVertexMeshComplex_X₂
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (x : Fin Q.length) :
    (rightVertexMeshComplex (K := K) G Q hAlt x).X₂ =
      middleObj (K := K) G Q hAlt x :=
  rfl

@[simp]
theorem rightVertexMeshComplex_X₃
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (x : Fin Q.length) :
    (rightVertexMeshComplex (K := K) G Q hAlt x).X₃ =
      RightRealization.vertexObj (K := K) G Q hAlt x :=
  rfl

@[simp]
theorem leftVertexMeshComplex_X₁
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (x : Fin Q.length) :
    (leftVertexMeshComplex (K := K) G Q hAlt x).X₁ =
      RightRealization.vertexObj (K := K) G Q hAlt x :=
  rfl

@[simp]
theorem leftVertexMeshComplex_X₂
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (x : Fin Q.length) :
    (leftVertexMeshComplex (K := K) G Q hAlt x).X₂ =
      outgoingMiddleObj (K := K) G Q hAlt x :=
  rfl

@[simp]
theorem leftVertexMeshComplex_X₃
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (x : Fin Q.length) :
    (leftVertexMeshComplex (K := K) G Q hAlt x).X₃ =
      nextObj (K := K) G Q hAlt x :=
  rfl

/-! ## Weak exactness on arbitrary matrix objects -/

/-- Singleton-source exactness extends rowwise to the weak-kernel property
of the right vertex mesh. -/
theorem rightVertexMesh_isWeakKernel
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (x : Fin Q.length) :
    ShortComplex.IsWeakKernel
      (rightVertexMeshComplex (K := K) G Q hAlt x) := by
  apply mat_isWeakKernel_of_exact_embedding
  intro s
  exact mat_exact_at_middle (K := K) G Q hAlt s x

/-- Singleton-target exactness extends columnwise to the weak-cokernel
property of the left vertex mesh. -/
theorem leftVertexMesh_isWeakCokernel
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (x : Fin Q.length) :
    ShortComplex.IsWeakCokernel
      (leftVertexMeshComplex (K := K) G Q hAlt x) := by
  apply mat_isWeakCokernel_of_exact_embedding
  intro t
  exact mat_exact_at_outgoing_middle (K := K) G Q hAlt x t

/-! ## Radical mesh arrows -/

/-- The predecessor-to-middle matrix is strictly forward, hence radical. -/
theorem previousToMiddle_isRadical
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (x : Fin Q.length) :
    IsRadicalMorphism (previousToMiddle (K := K) G Q hAlt x) := by
  rw [← mem_strictForwardIdeal_iff_isRadicalMorphism
    (K := K) G Q hAlt]
  change HasGap (K := K) G Q hAlt 1
    (previousToMiddle (K := K) G Q hAlt x)
  intro p y hpy
  change {p : Fin Q.length // IsPrevious Q p x} at p
  change {y : Fin Q.length // IsMiddle G Q y x} at y
  change ¬ (p.1.val + 1 ≤ y.1.val) at hpy
  exfalso
  apply hpy
  have hp_lt_y : p.1 < y.1 := y.2.2.2.1 p.1 p.2
  omega

/-- The incoming-middle-to-vertex matrix is strictly forward, hence
radical. -/
theorem middleToVertex_isRadical
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (x : Fin Q.length) :
    IsRadicalMorphism (middleToVertex (K := K) G Q hAlt x) := by
  rw [← mem_strictForwardIdeal_iff_isRadicalMorphism
    (K := K) G Q hAlt]
  change HasGap (K := K) G Q hAlt 1
    (middleToVertex (K := K) G Q hAlt x)
  intro y z hyx
  change {y : Fin Q.length // IsMiddle G Q y x} at y
  cases z
  change ¬ (y.1.val + 1 ≤ x.val) at hyx
  exfalso
  apply hyx
  have hy_lt_x : y.1 < x := y.2.2.1
  omega

/-- The vertex-to-outgoing-middle matrix is strictly forward, hence
radical. -/
theorem vertexToOutgoingMiddle_isRadical
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (x : Fin Q.length) :
    IsRadicalMorphism
      (vertexToOutgoingMiddle (K := K) G Q hAlt x) := by
  rw [← mem_strictForwardIdeal_iff_isRadicalMorphism
    (K := K) G Q hAlt]
  change HasGap (K := K) G Q hAlt 1
    (vertexToOutgoingMiddle (K := K) G Q hAlt x)
  intro z y hxy
  cases z
  change {y : Fin Q.length // IsMiddle G Q x y} at y
  change ¬ (x.val + 1 ≤ y.1.val) at hxy
  exfalso
  apply hxy
  have hx_lt_y : x < y.1 := y.2.2.1
  omega

/-- The outgoing-middle-to-next matrix is strictly forward, hence
radical. -/
theorem outgoingMiddleToNext_isRadical
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (x : Fin Q.length) :
    IsRadicalMorphism (outgoingMiddleToNext (K := K) G Q hAlt x) := by
  rw [← mem_strictForwardIdeal_iff_isRadicalMorphism
    (K := K) G Q hAlt]
  change HasGap (K := K) G Q hAlt 1
    (outgoingMiddleToNext (K := K) G Q hAlt x)
  intro y b hyb
  change {y : Fin Q.length // IsMiddle G Q x y} at y
  change {b : Fin Q.length // IsPrevious Q x b} at b
  change ¬ (y.1.val + 1 ≤ b.1.val) at hyb
  exfalso
  apply hyb
  have hy_middle_b : IsMiddle G Q y.1 b.1 :=
    (isMiddle_iff_previous_isMiddle hAlt b.2 y.1).mpr y.2
  have hy_lt_b : y.1 < b.1 := hy_middle_b.2.1
  omega

/-! ## Nonvanishing of paired mesh arrows -/

/-- Every first mesh arrow `p → y` is nonzero in the mesh quotient. -/
theorem quotientOutgoingMiddleArrow_ne_zero
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    {p y : Fin Q.length} (hpy : IsMiddle G Q p y) :
    quotientOutgoingMiddleArrow (K := K) G Q hAlt hpy ≠ 0 := by
  classical
  intro harrow
  let y₀ : {z : Fin Q.length // IsMiddle G Q p z} := ⟨y, hpy⟩
  let v : (z : {z : Fin Q.length // IsMiddle G Q p z}) →
      (WordMesh.obj (K := K) G Q hAlt z.1 ⟶
        WordMesh.obj (K := K) G Q hAlt y) :=
    fun z ↦ dite (z = y₀)
      (fun hz ↦ by
        subst z
        exact 𝟙 (WordMesh.obj (K := K) G Q hAlt y))
      (fun _ ↦ 0)
  have hout : quotientOutgoingMap (K := K) G Q hAlt p y v =
      quotientOutgoingMiddleArrow (K := K) G Q hAlt hpy := by
    change (∑ z, quotientOutgoingMiddleArrow (K := K) G Q hAlt z.2 ≫
      v z) = _
    rw [Finset.sum_eq_single y₀]
    · simp [v, y₀]
    · intro z hz hzy
      simp [v, hzy]
    · intro hy₀
      exact (hy₀ (Finset.mem_univ y₀)).elim
  have hvker : quotientOutgoingMap (K := K) G Q hAlt p y v = 0 := by
    rw [hout, harrow]
  obtain ⟨a, ha⟩ :=
    (quotient_exact_at_outgoing_middle (K := K) G Q hAlt p y v).mp
      hvker
  have ha0 : a = 0 := by
    funext c
    apply WordMesh.hom_eq_zero_of_not_le G Q hAlt
    have hyc : y < c.1 :=
      ((isMiddle_iff_previous_isMiddle hAlt c.2 y).mpr hpy).2.1
    exact not_le_of_gt hyc
  rw [ha0, map_zero] at ha
  have hv0 : v = 0 := ha.symm
  have hid : 𝟙 (WordMesh.obj (K := K) G Q hAlt y) = 0 := by
    have hy := congrFun hv0 y₀
    simpa [v, y₀] using hy
  have hcoord := congrArg
    (WordMesh.selfHomLinearEquiv (K := K) G Q hAlt y) hid
  simp [WordMesh.selfHomLinearEquiv_id] at hcoord

/-- The paired second mesh arrow `y → b` does not vanish in the mesh
quotient. -/
theorem quotientMiddleNextArrow_ne_zero_of_previous
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    {p y b : Fin Q.length}
    (hpb : IsPrevious Q p b) (hpy : IsMiddle G Q p y) :
    quotientMiddleNextArrow (K := K) G Q hAlt hpb hpy ≠ 0 := by
  classical
  intro harrow
  have hyb : IsMiddle G Q y b :=
    (isMiddle_iff_previous_isMiddle hAlt hpb y).mpr hpy
  let y₀ : {z : Fin Q.length // IsMiddle G Q z b} := ⟨y, hyb⟩
  let v : (z : {z : Fin Q.length // IsMiddle G Q z b}) →
      (WordMesh.obj (K := K) G Q hAlt y ⟶
        WordMesh.obj (K := K) G Q hAlt z.1) :=
    fun z ↦ dite (z = y₀)
      (fun hz ↦ by
        subst z
        exact 𝟙 (WordMesh.obj (K := K) G Q hAlt y))
      (fun _ ↦ 0)
  have hin : quotientIncomingMap (K := K) G Q hAlt y b v =
      quotientMiddleNextArrow (K := K) G Q hAlt hpb hpy := by
    change (∑ z, v z ≫ quotientMiddleArrow (K := K) G Q hAlt z.2) = _
    rw [Finset.sum_eq_single y₀]
    · simp [v, y₀, quotientMiddleNextArrow,
        pathMiddleNextArrow, quotientMiddleArrow]
    · intro z hz hzy
      simp [v, hzy]
    · intro hy₀
      exact (hy₀ (Finset.mem_univ y₀)).elim
  have hvker : quotientIncomingMap (K := K) G Q hAlt y b v = 0 := by
    rw [hin, harrow]
  obtain ⟨a, ha⟩ :=
    (quotient_exact_at_middle (K := K) G Q hAlt y b v).mp hvker
  have ha0 : a = 0 := by
    funext q
    apply WordMesh.hom_eq_zero_of_not_le G Q hAlt
    have hqp : q.1 = p := isPrevious_unique q.2 hpb
    rw [hqp]
    exact not_le_of_gt hpy.2.1
  rw [ha0, map_zero] at ha
  have hv0 : v = 0 := ha.symm
  have hid : 𝟙 (WordMesh.obj (K := K) G Q hAlt y) = 0 := by
    have hy := congrFun hv0 y₀
    simpa [v, y₀] using hy
  have hcoord := congrArg
    (WordMesh.selfHomLinearEquiv (K := K) G Q hAlt y) hid
  simp [WordMesh.selfHomLinearEquiv_id] at hcoord

/-! ## Minimality tools -/

/-- A matrix object with only one displayed index is isomorphic to that
displayed singleton summand. -/
def entryIsoOfSubsingleton
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    (X : AdditiveHull.Category (K := K) G Q hAlt)
    [Subsingleton X.ι] (i : X.ι) :
    (Mat_.embedding (WordMesh.Category (K := K) G Q hAlt)).obj (X.X i) ≅ X := by
  classical
  refine
    { hom := entryInclusion (K := K) G Q hAlt X i
      inv := entryProjection (K := K) G Q hAlt X i
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply Mat_.hom_ext
    intro a b
    cases a
    cases b
    simp only [entryInclusion, entryProjection, Mat_.comp_apply,
      Mat_.id_apply_self]
    change (∑ k : X.ι, (𝟙 X) i k ≫ (𝟙 X) k i) = 𝟙 (X.X i)
    rw [Finset.sum_eq_single i]
    · simp
    · intro k hk hki
      exact (hki (Subsingleton.elim k i)).elim
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  · apply Mat_.hom_ext
    intro a b
    have hai : a = i := Subsingleton.elim _ _
    have hbi : b = i := Subsingleton.elim _ _
    subst a
    subst b
    simp only [entryInclusion, entryProjection, Mat_.comp_apply,
      Mat_.id_apply_self]
    dsimp only [Mat_.embedding]
    change (∑ _ : PUnit, 𝟙 (X.X i) ≫ 𝟙 (X.X i)) = 𝟙 (X.X i)
    rw [Finset.univ_unique]
    simp

/-- A displayed summand inclusion is invertible when the matrix object has
only one index. -/
theorem entryInclusion_isIso_of_subsingleton
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    (X : AdditiveHull.Category (K := K) G Q hAlt)
    [Subsingleton X.ι] (i : X.ι) :
    IsIso (entryInclusion (K := K) G Q hAlt X i) := by
  change IsIso (entryIsoOfSubsingleton (K := K) G Q hAlt X i).hom
  infer_instance

/-- A displayed summand projection is invertible when the matrix object has
only one index. -/
theorem entryProjection_isIso_of_subsingleton
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    (X : AdditiveHull.Category (K := K) G Q hAlt)
    [Subsingleton X.ι] (i : X.ι) :
    IsIso (entryProjection (K := K) G Q hAlt X i) := by
  change IsIso (entryIsoOfSubsingleton (K := K) G Q hAlt X i).inv
  infer_instance

/-- A nonzero map from a singleton word vertex is right minimal. -/
theorem isRightMinimal_of_vertex_source_ne_zero
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    (x : Fin Q.length)
    {Y : AdditiveHull.Category (K := K) G Q hAlt}
    (f : AdditiveHull.vertexObj (K := K) G Q hAlt x ⟶ Y)
    (hf : f ≠ 0) : IsRightMinimal f := by
  intro e he
  apply vertexEnd_isIso_of_ne_zero (K := K) G Q hAlt x e
  intro he0
  apply hf
  calc
    f = e ≫ f := he.symm
    _ = (0 : AdditiveHull.vertexObj (K := K) G Q hAlt x ⟶
        AdditiveHull.vertexObj (K := K) G Q hAlt x) ≫ f :=
      congrArg (fun q ↦ q ≫ f) he0
    _ = 0 := by simp

/-- A nonzero map into a singleton word vertex is left minimal. -/
theorem isLeftMinimal_of_vertex_target_ne_zero
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    (x : Fin Q.length)
    {Y : AdditiveHull.Category (K := K) G Q hAlt}
    (f : Y ⟶ AdditiveHull.vertexObj (K := K) G Q hAlt x)
    (hf : f ≠ 0) : IsLeftMinimal f := by
  intro e he
  apply vertexEnd_isIso_of_ne_zero (K := K) G Q hAlt x e
  intro he0
  apply hf
  calc
    f = f ≫ e := he.symm
    _ = f ≫ (0 : AdditiveHull.vertexObj (K := K) G Q hAlt x ⟶
        AdditiveHull.vertexObj (K := K) G Q hAlt x) :=
      congrArg (fun q ↦ f ≫ q) he0
    _ = 0 := by simp

/-- If postcomposition with an isomorphism is left minimal, then the
original morphism is left minimal. -/
theorem isLeftMinimal_of_postcomp_isIso
    {C : Type*} [CategoryTheory.Category C]
    {X Y Z : C} (g : X ⟶ Y) (j : Y ⟶ Z) [IsIso j]
    (hgj : IsLeftMinimal (g ≫ j)) : IsLeftMinimal g := by
  intro e he
  let e' : Z ⟶ Z := inv j ≫ e ≫ j
  have he' : (g ≫ j) ≫ e' = g ≫ j := by
    calc
      (g ≫ j) ≫ e' = (g ≫ e) ≫ j := by simp [e', Category.assoc]
      _ = g ≫ j := by rw [he]
  letI : IsIso e' := hgj e' he'
  have heq : e = j ≫ e' ≫ inv j := by
    simp [e', Category.assoc]
  rw [heq]
  infer_instance

/-! ## Minimality of the two mesh-boundary maps -/

/-- Under a positive right-additive weight, the predecessor-to-middle map
of every right vertex mesh is right minimal. -/
theorem previousToMiddle_isRightMinimal
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    (weight : Fin Q.length → ℤ)
    (hweight : IsPositiveRightAdditive G Q weight)
    (x : Fin Q.length) :
    IsRightMinimal (previousToMiddle (K := K) G Q hAlt x) := by
  classical
  by_cases hprev : ∃ p, IsPrevious Q p x
  · obtain ⟨p, hp⟩ := hprev
    obtain ⟨y, hy⟩ :=
      Word.nonprojective_hasIncoming_of_positiveRightAdditive G Q weight hweight
        ⟨x, ⟨p, hp⟩⟩
    let p₀ : {q : Fin Q.length // IsPrevious Q q x} := ⟨p, hp⟩
    let y₀ : {z : Fin Q.length // IsMiddle G Q z x} := ⟨y, hy⟩
    letI : Subsingleton (previousObj (K := K) G Q hAlt x).ι :=
      ⟨fun a b ↦ Subtype.ext (isPrevious_unique a.2 b.2)⟩
    let e := entryIsoOfSubsingleton (K := K) G Q hAlt
      (previousObj (K := K) G Q hAlt x) p₀
    have hcomp_ne :
        e.hom ≫ previousToMiddle (K := K) G Q hAlt x ≠ 0 := by
      intro hzero
      have hcut :
          e.hom ≫ previousToMiddle (K := K) G Q hAlt x ≫
              entryProjection (K := K) G Q hAlt
                (middleObj (K := K) G Q hAlt x) y₀ = 0 := by
        rw [← Category.assoc, hzero, zero_comp]
      change entryInclusion (K := K) G Q hAlt
          (previousObj (K := K) G Q hAlt x) p₀ ≫
            previousToMiddle (K := K) G Q hAlt x ≫
              entryProjection (K := K) G Q hAlt
                (middleObj (K := K) G Q hAlt x) y₀ = 0 at hcut
      rw [entryInclusion_comp_comp_entryProjection] at hcut
      have hentry := congrFun (congrFun hcut PUnit.unit) PUnit.unit
      change previousToMiddle (K := K) G Q hAlt x p₀ y₀ = 0 at hentry
      have harrow :
          quotientPreviousMiddleArrow (K := K) G Q hAlt hp hy = 0 := by
        change quotientPreviousMiddleArrow (K := K) G Q hAlt hp hy = 0 at hentry
        exact hentry
      apply quotientOutgoingMiddleArrow_ne_zero (K := K) G Q hAlt
        (previous_isMiddle_of_isMiddle hAlt hp hy)
      simpa only [quotientPreviousMiddleArrow, pathPreviousMiddleArrow,
        quotientOutgoingMiddleArrow] using harrow
    have hcomp_min : IsRightMinimal
        (e.hom ≫ previousToMiddle (K := K) G Q hAlt x) :=
      isRightMinimal_of_vertex_source_ne_zero (K := K) G Q hAlt p
        (e.hom ≫ previousToMiddle (K := K) G Q hAlt x) hcomp_ne
    have hmin := hcomp_min.precomp_splitMono e.inv
    simpa [e, Category.assoc] using hmin
  · have hzero := previousObj_isZero_of_first
      (K := K) G Q hAlt x hprev
    intro a ha
    have haid : a = 𝟙 (previousObj (K := K) G Q hAlt x) :=
      hzero.eq_of_src a (𝟙 _)
    rw [haid]
    infer_instance

/-- Under a positive right-additive weight, the outgoing-middle-to-next map
of every left vertex mesh is left minimal. -/
theorem outgoingMiddleToNext_isLeftMinimal
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    (weight : Fin Q.length → ℤ)
    (hweight : IsPositiveRightAdditive G Q weight)
    (x : Fin Q.length) :
    IsLeftMinimal (outgoingMiddleToNext (K := K) G Q hAlt x) := by
  classical
  by_cases hnext : ∃ b, IsPrevious Q x b
  · obtain ⟨b, hb⟩ := hnext
    obtain ⟨y, hyb⟩ :=
      Word.nonprojective_hasIncoming_of_positiveRightAdditive G Q weight
        hweight ⟨b, ⟨x, hb⟩⟩
    have hxy : IsMiddle G Q x y :=
      (isMiddle_iff_previous_isMiddle hAlt hb y).mp hyb
    let y₀ : (outgoingMiddleObj (K := K) G Q hAlt x).ι := ⟨y, hxy⟩
    let b₀ : (nextObj (K := K) G Q hAlt x).ι := ⟨b, hb⟩
    letI : Subsingleton (nextObj (K := K) G Q hAlt x).ι :=
      ⟨fun a c ↦ Subtype.ext (Word.isPrevious_target_unique a.2 c.2)⟩
    let e := entryIsoOfSubsingleton (K := K) G Q hAlt
      (nextObj (K := K) G Q hAlt x) b₀
    have hcomp_ne :
        outgoingMiddleToNext (K := K) G Q hAlt x ≫ e.inv ≠ 0 := by
      intro hzero
      have hcut :
          entryInclusion (K := K) G Q hAlt
              (outgoingMiddleObj (K := K) G Q hAlt x) y₀ ≫
            outgoingMiddleToNext (K := K) G Q hAlt x ≫ e.inv = 0 := by
        rw [hzero, comp_zero]
      change entryInclusion (K := K) G Q hAlt
          (outgoingMiddleObj (K := K) G Q hAlt x) y₀ ≫
            outgoingMiddleToNext (K := K) G Q hAlt x ≫
              entryProjection (K := K) G Q hAlt
                (nextObj (K := K) G Q hAlt x) b₀ = 0 at hcut
      rw [entryInclusion_comp_comp_entryProjection] at hcut
      have hentry := congrFun (congrFun hcut PUnit.unit) PUnit.unit
      change outgoingMiddleToNext (K := K) G Q hAlt x y₀ b₀ = 0 at hentry
      change quotientMiddleNextArrow (K := K) G Q hAlt hb hxy = 0 at hentry
      exact quotientMiddleNextArrow_ne_zero_of_previous
        (K := K) G Q hAlt hb hxy hentry
    have hcomp_min : IsLeftMinimal
        (outgoingMiddleToNext (K := K) G Q hAlt x ≫ e.inv) :=
      isLeftMinimal_of_vertex_target_ne_zero (K := K) G Q hAlt b
        (outgoingMiddleToNext (K := K) G Q hAlt x ≫ e.inv) hcomp_ne
    exact isLeftMinimal_of_postcomp_isIso
      (outgoingMiddleToNext (K := K) G Q hAlt x) e.inv hcomp_min
  · have hzero := nextObj_isZero_of_last
      (K := K) G Q hAlt x hnext
    intro a ha
    have haid : a = 𝟙 (nextObj (K := K) G Q hAlt x) :=
      hzero.eq_of_tgt a (𝟙 _)
    rw [haid]
    infer_instance

/-! ## The two endpoint radical factorization properties -/

/-- Every radical morphism into the endpoint vertex of a right mesh factors
through its middle-to-vertex map. -/
theorem rightVertex_factors_into_right
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (x : Fin Q.length)
    {W : AdditiveHull.Category (K := K) G Q hAlt}
    (a : W ⟶ RightRealization.vertexObj (K := K) G Q hAlt x)
    (ha : IsRadicalMorphism a) :
    ∃ b : W ⟶ middleObj (K := K) G Q hAlt x,
      b ≫ middleToVertex (K := K) G Q hAlt x = a := by
  classical
  let row (i : W.ι) :
      RightRealization.vertexObj (K := K) G Q hAlt (W.X i) ⟶
        RightRealization.vertexObj (K := K) G Q hAlt x :=
    fun _ _ ↦ a i PUnit.unit
  have hquot (i : W.ι) :
      matSimpleQuotient (K := K) G Q hAlt (W.X i) x (row i) = 0 := by
    let s : Fin Q.length := W.X i
    change quotientSimpleMap (K := K) G Q hAlt s x
      (a i PUnit.unit) = 0
    by_cases hi : s = x
    · have hentry : a i PUnit.unit = 0 :=
        equal_entries_zero_of_isRadicalMorphism
          (K := K) G Q hAlt a ha i PUnit.unit (by
            change (show Fin Q.length from W.X i) = x
            simpa [s] using hi)
      rw [hentry]
      exact map_zero _
    · funext q
      exact Fin.elim0 (by
        simpa [SimpleRepresentableFiber, hi] using q)
  choose b hb using fun i ↦
    (mat_exact_at_right (K := K) G Q hAlt (W.X i) x (row i)).mp
      (hquot i)
  let lift : W ⟶ middleObj (K := K) G Q hAlt x :=
    fun i y ↦ b i PUnit.unit y
  refine ⟨lift, ?_⟩
  apply Mat_.hom_ext
  intro i z
  cases z
  exact congrFun (congrFun (hb i) PUnit.unit) PUnit.unit

/-- Every radical morphism out of the initial vertex of a left mesh factors
through its vertex-to-outgoing-middle map. -/
theorem leftVertex_factors_from_left
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (x : Fin Q.length)
    {W : AdditiveHull.Category (K := K) G Q hAlt}
    (a : RightRealization.vertexObj (K := K) G Q hAlt x ⟶ W)
    (ha : IsRadicalMorphism a) :
    ∃ b : outgoingMiddleObj (K := K) G Q hAlt x ⟶ W,
      vertexToOutgoingMiddle (K := K) G Q hAlt x ≫ b = a := by
  classical
  let column (j : W.ι) :
      RightRealization.vertexObj (K := K) G Q hAlt x ⟶
        RightRealization.vertexObj (K := K) G Q hAlt (W.X j) :=
    fun _ _ ↦ a PUnit.unit j
  have hquot (j : W.ι) :
      matCosimpleQuotient (K := K) G Q hAlt x (W.X j) (column j) = 0 := by
    let t : Fin Q.length := W.X j
    change quotientCosimpleMap (K := K) G Q hAlt x t
      (a PUnit.unit j) = 0
    by_cases hj : x = t
    · have hentry : a PUnit.unit j = 0 :=
        equal_entries_zero_of_isRadicalMorphism
          (K := K) G Q hAlt a ha PUnit.unit j (by
            change x = (show Fin Q.length from W.X j)
            simpa [t] using hj)
      rw [hentry]
      exact map_zero _
    · funext q
      exact Fin.elim0 (by
        simpa [SimpleCorepresentableFiber, hj] using q)
  choose b hb using fun j ↦
    (mat_exact_at_source (K := K) G Q hAlt x (W.X j) (column j)).mp
      (hquot j)
  let lift : outgoingMiddleObj (K := K) G Q hAlt x ⟶ W :=
    fun y j ↦ b j y PUnit.unit
  refine ⟨lift, ?_⟩
  apply Mat_.hom_ext
  intro z j
  cases z
  exact congrFun (congrFun (hb j) PUnit.unit) PUnit.unit

/-! ## The translated endpoint factorization properties -/

/-- A radical morphism out of the predecessor term of a right mesh factors
through its first mesh map.  The proof identifies that mesh with the left
mesh beginning at the unique predecessor. -/
theorem rightVertex_factors_from_left
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (x : Fin Q.length)
    {W : AdditiveHull.Category (K := K) G Q hAlt}
    (a : previousObj (K := K) G Q hAlt x ⟶ W)
    (ha : IsRadicalMorphism a) :
    ∃ b : middleObj (K := K) G Q hAlt x ⟶ W,
      previousToMiddle (K := K) G Q hAlt x ≫ b = a := by
  classical
  by_cases hprev : ∃ p, IsPrevious Q p x
  · obtain ⟨p, hp⟩ := hprev
    let p₀ : {q : Fin Q.length // IsPrevious Q q x} := ⟨p, hp⟩
    let column (j : W.ι) :
        RightRealization.vertexObj (K := K) G Q hAlt p ⟶
          RightRealization.vertexObj (K := K) G Q hAlt (W.X j) :=
      fun _ _ ↦ a p₀ j
    have hcolumn (j : W.ι) : IsRadicalMorphism (column j) := by
      have hpre : IsRadicalMorphism
          (entryInclusion (K := K) G Q hAlt
            (previousObj (K := K) G Q hAlt x) p₀ ≫ a) :=
        isRadicalMorphism_precomp _ ha
      have hcomp : IsRadicalMorphism
          (entryInclusion (K := K) G Q hAlt
              (previousObj (K := K) G Q hAlt x) p₀ ≫ a ≫
            entryProjection (K := K) G Q hAlt W j) := by
        simpa only [Category.assoc] using
          isRadicalMorphism_postcomp
            (entryProjection (K := K) G Q hAlt W j) hpre
      rw [entryInclusion_comp_comp_entryProjection] at hcomp
      change IsRadicalMorphism
        ((Mat_.embedding (WordMesh.Category (K := K) G Q hAlt)).map
          (a p₀ j))
      exact hcomp
    choose c hc using fun j ↦
      leftVertex_factors_from_left (K := K) G Q hAlt p
        (column j) (hcolumn j)
    let e := outgoingMiddleEquivIncoming G Q hAlt hp
    let lift : middleObj (K := K) G Q hAlt x ⟶ W :=
      fun y j ↦ c j (e.symm y) PUnit.unit
    refine ⟨lift, ?_⟩
    apply Mat_.hom_ext
    intro q j
    change {q : Fin Q.length // IsPrevious Q q x} at q
    have hq : q = p₀ := Subtype.ext (isPrevious_unique q.2 hp)
    subst q
    have hj := congrFun (congrFun (hc j) PUnit.unit) PUnit.unit
    change (∑ y : {y : Fin Q.length // IsMiddle G Q p y},
        quotientOutgoingMiddleArrow (K := K) G Q hAlt y.2 ≫
          c j y PUnit.unit) = a p₀ j at hj
    change (∑ y : {y : Fin Q.length // IsMiddle G Q y x},
        quotientPreviousMiddleArrow (K := K) G Q hAlt hp y.2 ≫
          c j (e.symm y) PUnit.unit) = a p₀ j
    rw [← hj]
    apply Fintype.sum_equiv e.symm
    intro y
    rfl
  · have hzero := previousObj_isZero_of_first
      (K := K) G Q hAlt x hprev
    have ha0 : a = 0 := hzero.eq_of_src a 0
    refine ⟨0, ?_⟩
    rw [ha0]
    simp

/-- A radical morphism into the next-occurrence term of a left mesh factors
through its second mesh map.  The proof identifies that mesh with the right
mesh ending at the unique next occurrence. -/
theorem leftVertex_factors_into_right
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (x : Fin Q.length)
    {W : AdditiveHull.Category (K := K) G Q hAlt}
    (a : W ⟶ nextObj (K := K) G Q hAlt x)
    (ha : IsRadicalMorphism a) :
    ∃ b : W ⟶ outgoingMiddleObj (K := K) G Q hAlt x,
      b ≫ outgoingMiddleToNext (K := K) G Q hAlt x = a := by
  classical
  by_cases hnext : ∃ b, IsPrevious Q x b
  · obtain ⟨b, hb⟩ := hnext
    let b₀ : {c : Fin Q.length // IsPrevious Q x c} := ⟨b, hb⟩
    let row (i : W.ι) :
        RightRealization.vertexObj (K := K) G Q hAlt (W.X i) ⟶
          RightRealization.vertexObj (K := K) G Q hAlt b :=
      fun _ _ ↦ a i b₀
    have hrow (i : W.ι) : IsRadicalMorphism (row i) := by
      have hpre : IsRadicalMorphism
          (entryInclusion (K := K) G Q hAlt W i ≫ a) :=
        isRadicalMorphism_precomp _ ha
      have hcomp : IsRadicalMorphism
          (entryInclusion (K := K) G Q hAlt W i ≫ a ≫
            entryProjection (K := K) G Q hAlt
              (nextObj (K := K) G Q hAlt x) b₀) := by
        simpa only [Category.assoc] using
          isRadicalMorphism_postcomp
            (entryProjection (K := K) G Q hAlt
              (nextObj (K := K) G Q hAlt x) b₀) hpre
      rw [entryInclusion_comp_comp_entryProjection] at hcomp
      change IsRadicalMorphism
        ((Mat_.embedding (WordMesh.Category (K := K) G Q hAlt)).map
          (a i b₀))
      exact hcomp
    choose c hc using fun i ↦
      rightVertex_factors_into_right (K := K) G Q hAlt b
        (row i) (hrow i)
    let e := outgoingMiddleEquivIncoming G Q hAlt hb
    let lift : W ⟶ outgoingMiddleObj (K := K) G Q hAlt x :=
      fun i y ↦ c i PUnit.unit (e y)
    refine ⟨lift, ?_⟩
    apply Mat_.hom_ext
    intro i q
    change {q : Fin Q.length // IsPrevious Q x q} at q
    have hqb : q.1 = b := by
      rcases lt_trichotomy q.1 b with hqb | hqb | hbq
      · exact False.elim
          (hb.2.2 q.1 q.2.1 hqb
            (q.2.2.1.symm.trans hb.2.1))
      · exact hqb
      · exact False.elim
          (q.2.2.2 b hb.1 hbq
            (hb.2.1.symm.trans q.2.2.1))
    have hq : q = b₀ := Subtype.ext hqb
    subst q
    have hi := congrFun (congrFun (hc i) PUnit.unit) PUnit.unit
    change (∑ y : {y : Fin Q.length // IsMiddle G Q y b},
        c i PUnit.unit y ≫
          quotientMiddleArrow (K := K) G Q hAlt y.2) = a i b₀ at hi
    change (∑ y : {y : Fin Q.length // IsMiddle G Q x y},
        c i PUnit.unit (e y) ≫
          quotientMiddleNextArrow (K := K) G Q hAlt hb y.2) = a i b₀
    rw [← hi]
    apply Fintype.sum_equiv e
    intro y
    rfl
  · have hzero := nextObj_isZero_of_last
      (K := K) G Q hAlt x hnext
    have ha0 : a = 0 := hzero.eq_of_tgt a 0
    refine ⟨0, ?_⟩
    rw [ha0]
    simp

/-! ## Vertex tau-sequences -/

/-- Every right vertex mesh is a right tau-sequence when the word admits a
positive right-additive weight. -/
theorem rightVertexTauSequence
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    (weight : Fin Q.length → ℤ)
    (hweight : IsPositiveRightAdditive G Q weight)
    (x : Fin Q.length) :
    RightTauSequence (rightVertexMeshComplex (K := K) G Q hAlt x) where
  toTauApproximation :=
    { f_radical := previousToMiddle_isRadical (K := K) G Q hAlt x
      g_radical := middleToVertex_isRadical (K := K) G Q hAlt x
      factors_from_left := fun a ha ↦
        rightVertex_factors_from_left (K := K) G Q hAlt x a ha
      factors_into_right := fun a ha ↦
        rightVertex_factors_into_right (K := K) G Q hAlt x a ha }
  minimalWeakKernel :=
    ⟨rightVertexMesh_isWeakKernel (K := K) G Q hAlt x,
      previousToMiddle_isRightMinimal (K := K) G Q hAlt weight hweight x⟩

/-- Every left vertex mesh is a left tau-sequence when the word admits a
positive right-additive weight. -/
theorem leftVertexTauSequence
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    (weight : Fin Q.length → ℤ)
    (hweight : IsPositiveRightAdditive G Q weight)
    (x : Fin Q.length) :
    LeftTauSequence (leftVertexMeshComplex (K := K) G Q hAlt x) where
  toTauApproximation :=
    { f_radical := vertexToOutgoingMiddle_isRadical (K := K) G Q hAlt x
      g_radical := outgoingMiddleToNext_isRadical (K := K) G Q hAlt x
      factors_from_left := fun a ha ↦
        leftVertex_factors_from_left (K := K) G Q hAlt x a ha
      factors_into_right := fun a ha ↦
        leftVertex_factors_into_right (K := K) G Q hAlt x a ha }
  minimalWeakCokernel :=
    ⟨leftVertexMesh_isWeakCokernel (K := K) G Q hAlt x,
      outgoingMiddleToNext_isLeftMinimal (K := K) G Q hAlt weight hweight x⟩

end OpConjecture.RepresentationDirected.IyamaMesh.WordMesh.TauSequences
