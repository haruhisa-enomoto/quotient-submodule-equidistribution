import QuotientSubmoduleEquidistribution.RepresentationDirected.IyamaWordMeshStartingRecurrence

/-!
# Outgoing quotient-Hom exactness for the word mesh category

This file proves the target-evaluated, source-oriented counterpart of
`IyamaWordMeshRecurrence`, using the first-arrow normal form for the word
mesh ideal. It supplies the vertexwise exactness needed to construct left
tau-sequences after finite-biproduct transport.

Everything here is abstract: no concrete algebra, quiver instance, module
enumeration, or classification is used.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open CategoryTheory

namespace QuotientSubmoduleEquidistribution.RepresentationDirected.IyamaMesh.WordMeshStartingExactness

open QuotientSubmoduleEquidistribution.CategoricalIdeal
open QuotientSubmoduleEquidistribution.RepresentationDirected.ARWord
open QuotientSubmoduleEquidistribution.RepresentationDirected.IyamaMesh.WordPath
open QuotientSubmoduleEquidistribution.RepresentationDirected.IyamaMesh.WordMesh
open QuotientSubmoduleEquidistribution.RepresentationDirected.IyamaMesh.WordMeshStartingRecurrence

universe uK uL uV

variable {K : Type uK} [Field K]
variable {L : Type uL}

/-- The image in the mesh category of one outgoing middle arrow. -/
def quotientOutgoingMiddleArrow
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    {x y : Fin Q.length} (hxy : IsMiddle G Q x y) :
    WordMesh.obj (K := K) G Q hAlt x ⟶
      WordMesh.obj (K := K) G Q hAlt y :=
  WordMesh.quotientHom (K := K) G Q hAlt
    (WordPath.middleArrow (K := K) G Q hxy)

/-- Evaluation against a fixed target of the map formed by all outgoing
middle arrows at `x`. -/
def quotientOutgoingMap
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    (x t : Fin Q.length) :
    ((y : {y : Fin Q.length // IsMiddle G Q x y}) →
      (WordMesh.obj (K := K) G Q hAlt y.1 ⟶
        WordMesh.obj (K := K) G Q hAlt t)) →ₗ[K]
      (WordMesh.obj (K := K) G Q hAlt x ⟶
        WordMesh.obj (K := K) G Q hAlt t) where
  toFun g := ∑ y, quotientOutgoingMiddleArrow (K := K) G Q hAlt y.2 ≫ g y
  map_add' := by
    intro f g
    simp only [Pi.add_apply, Preadditive.comp_add, Finset.sum_add_distrib]
  map_smul' := by
    intro k f
    simp only [Pi.smul_apply, Linear.comp_smul, Finset.smul_sum,
      RingHom.id_apply]

/-- A one-dimensional diagonal fiber and zero off the diagonal, interpreted
as the simple corepresentable evaluated at a target vertex. -/
abbrev SimpleCorepresentableFiber (K : Type uK) [Field K]
    {V : Type uV} [DecidableEq V] (x t : V) : Type uK :=
  Fin (if x = t then 1 else 0) → K

/-- The diagonal simple quotient of the corepresentable at `x`. -/
def quotientCosimpleMap
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    (x t : Fin Q.length) :
    (WordMesh.obj (K := K) G Q hAlt x ⟶
      WordMesh.obj (K := K) G Q hAlt t) →ₗ[K]
      SimpleCorepresentableFiber K x t := by
  classical
  by_cases hxt : x = t
  · subst t
    exact
      { toFun := fun f _ ↦ WordMesh.selfHomLinearEquiv
          (K := K) G Q hAlt x f
        map_add' := by intros; ext i; simp
        map_smul' := by intros; ext i; simp }
  · exact 0

/-- The diagonal simple corepresentable quotient is onto. -/
theorem quotientCosimpleMap_surjective
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    (x t : Fin Q.length) :
    Function.Surjective (quotientCosimpleMap (K := K) G Q hAlt x t) := by
  classical
  by_cases hxt : x = t
  · subst t
    intro q
    let i₀ : Fin (if x = x then 1 else 0) := ⟨0, by simp⟩
    refine ⟨q i₀ • 𝟙 (WordMesh.obj (K := K) G Q hAlt x), ?_⟩
    funext i
    have hi : i = i₀ := by
      apply Fin.ext
      change i.val = 0
      have hiBound : i.val < 1 := by simpa [if_pos rfl] using i.isLt
      omega
    subst i
    simp [quotientCosimpleMap, WordMesh.selfHomLinearEquiv_id]
  · intro q
    refine ⟨0, ?_⟩
    funext i
    exact Fin.elim0 (show Fin 0 from
      (by simpa [SimpleCorepresentableFiber, hxt]
        using i))

/-- Vanishing in the mesh quotient is exactly membership in the generated
mesh ideal. -/
theorem quotientHom_eq_zero_iff
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    {x t : Fin Q.length}
    (f : WordPath.obj K G Q x ⟶ WordPath.obj K G Q t) :
    WordMesh.quotientHom (K := K) G Q hAlt f = 0 ↔
      f ∈ (WordMesh.meshIdeal (K := K) G Q hAlt).hom
        (WordPath.obj K G Q x) (WordPath.obj K G Q t) := by
  constructor
  · intro hf
    apply ((WordMesh.meshIdeal (K := K) G Q hAlt).map_eq_zero_iff f).mp
    have hf0 : WordMesh.quotientHom (K := K) G Q hAlt f =
        WordMesh.quotientHom (K := K) G Q hAlt
          (0 : WordPath.obj K G Q x ⟶ WordPath.obj K G Q t) := by
      simpa using hf
    have hmap := congrArg InducedCategory.Hom.hom hf0
    change (WordMesh.quotientFunctor (K := K) G Q hAlt).map f =
      (WordMesh.quotientFunctor (K := K) G Q hAlt).map 0 at hmap
    simpa using hmap
  · intro hf
    apply InducedCategory.hom_ext
    exact ((WordMesh.meshIdeal (K := K) G Q hAlt).map_eq_zero_iff f).mpr hf

/-- Every nontrivial path-basis class lies in the image of the evaluated
outgoing-arrow map. -/
theorem quotient_pathHom_mem_range_outgoing_of_ne
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    {x t : Fin Q.length} (hxt : x ≠ t)
    (p : Quiver.Path (WordPath.vertex G Q t) (WordPath.vertex G Q x)) :
    WordMesh.quotientHom (K := K) G Q hAlt (WordPath.pathHom G Q p) ∈
      LinearMap.range (quotientOutgoingMap (K := K) G Q hAlt x t) := by
  classical
  rcases pathHom_eq_id_or_factor_firstMiddle (K := K) G Q p with
      hp0 | hfactor
  · have hv : WordPath.vertex G Q t = WordPath.vertex G Q x :=
      Quiver.Path.eq_of_length_zero p hp0
    have htx : t = x := congrArg WordPath.ReverseWordQuiver.pos hv
    exact False.elim (hxt htx.symm)
  · rcases hfactor with ⟨y, hxy, g, hpath⟩
    let y₀ : {z : Fin Q.length // IsMiddle G Q x z} := ⟨y, hxy⟩
    let d : ∀ z : {z : Fin Q.length // IsMiddle G Q x z},
        WordMesh.obj (K := K) G Q hAlt z.1 ⟶
          WordMesh.obj (K := K) G Q hAlt t :=
      fun z ↦ dite (z = y₀)
        (fun h ↦ by
          subst z
          exact WordMesh.quotientHom (K := K) G Q hAlt g)
        (fun _ ↦ 0)
    refine ⟨d, ?_⟩
    change (∑ z, quotientOutgoingMiddleArrow (K := K) G Q hAlt z.2 ≫ d z) = _
    have hsum :
        (∑ z, quotientOutgoingMiddleArrow (K := K) G Q hAlt z.2 ≫ d z) =
          quotientOutgoingMiddleArrow (K := K) G Q hAlt hxy ≫
            WordMesh.quotientHom (K := K) G Q hAlt g := by
      calc
        _ = quotientOutgoingMiddleArrow (K := K) G Q hAlt y₀.2 ≫ d y₀ := by
          apply Finset.sum_eq_single y₀
          · intro z _ hz
            simp [d, hz]
          · intro hy₀
            exact (hy₀ (Finset.mem_univ y₀)).elim
        _ = _ := by simp [d, y₀]
    rw [hsum, quotientOutgoingMiddleArrow, ← WordMesh.quotientHom_comp,
      ← hpath]
    rfl

/-- Off the diagonal, the evaluated outgoing-arrow map is surjective. -/
theorem quotientOutgoingMap_surjective_of_ne
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    {x t : Fin Q.length} (hxt : x ≠ t) :
    Function.Surjective (quotientOutgoingMap (K := K) G Q hAlt x t) := by
  intro f
  obtain ⟨v, rfl⟩ := WordMesh.quotientHom_surjective
    (K := K) G Q hAlt x t f
  letI : Fintype
      (Quiver.Path
        (WordPath.vertex G Q (WordPath.obj K G Q t))
        (WordPath.vertex G Q (WordPath.obj K G Q x))) :=
    Fintype.ofFinite _
  change (WordMesh.quotientHomLinearMap (K := K) G Q hAlt x t) v ∈
    LinearMap.range (quotientOutgoingMap (K := K) G Q hAlt x t)
  rw [← (WordPath.homPathBasis G Q
    (WordPath.obj K G Q x) (WordPath.obj K G Q t)).sum_repr v]
  rw [map_sum]
  apply Submodule.sum_mem
  intro p hp
  rw [map_smul]
  apply Submodule.smul_mem
  rw [homPathBasis_apply]
  exact quotient_pathHom_mem_range_outgoing_of_ne G Q hAlt hxt p

/-- The outgoing-arrow image is annihilated by the diagonal simple
corepresentable quotient. -/
theorem quotientCosimpleMap_outgoing_eq_zero
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    (x t : Fin Q.length)
    (g : (y : {y : Fin Q.length // IsMiddle G Q x y}) →
      (WordMesh.obj (K := K) G Q hAlt y.1 ⟶
        WordMesh.obj (K := K) G Q hAlt t)) :
    quotientCosimpleMap (K := K) G Q hAlt x t
      (quotientOutgoingMap (K := K) G Q hAlt x t g) = 0 := by
  classical
  by_cases hxt : x = t
  · subst t
    have hg : g = 0 := by
      funext y
      exact WordMesh.hom_eq_zero_of_not_le G Q hAlt
        (not_le_of_gt y.2.2.1) (g y)
    subst g
    simp [quotientOutgoingMap]
  · simp [quotientCosimpleMap, hxt]

/-- Exactness at the source-vertex corepresentable term of the raw word mesh
category. -/
theorem quotient_exact_at_source
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    (x t : Fin Q.length) :
    Function.Exact
      (quotientOutgoingMap (K := K) G Q hAlt x t)
      (quotientCosimpleMap (K := K) G Q hAlt x t) := by
  intro f
  constructor
  · intro hf
    by_cases hxt : x = t
    · subst t
      let i₀ : Fin (if x = x then 1 else 0) := ⟨0, by simp⟩
      have hcoord : WordMesh.selfHomLinearEquiv
          (K := K) G Q hAlt x f = 0 := by
        have hi := congrFun hf i₀
        simpa [quotientCosimpleMap, i₀] using hi
      have hfzero : f = 0 := by
        apply (WordMesh.selfHomLinearEquiv (K := K) G Q hAlt x).injective
        simpa using hcoord
      subst f
      exact ⟨0, by simp [quotientOutgoingMap]⟩
    · exact quotientOutgoingMap_surjective_of_ne G Q hAlt hxt f
  · rintro ⟨g, rfl⟩
    exact quotientCosimpleMap_outgoing_eq_zero G Q hAlt x t g

/-! ## Freeness of the outgoing-arrow map before quotienting -/

/-- Append the reverse of an outgoing middle arrow to a reverse-quiver path. -/
def appendMiddlePath
    (G : SimpleGraph L) (Q : List L)
    {x t : Fin Q.length}
    (s : Σ y : {y : Fin Q.length // IsMiddle G Q x y},
      Quiver.Path (WordPath.vertex G Q t) (WordPath.vertex G Q y.1)) :
    Quiver.Path (WordPath.vertex G Q t) (WordPath.vertex G Q x) :=
  s.2.comp (WordPath.reverseArrowPath G Q s.1.2)

/-- Different outgoing arrows, preceded by arbitrary reverse paths, produce
different paths. -/
theorem appendMiddlePath_injective
    (G : SimpleGraph L) (Q : List L)
    (x t : Fin Q.length) :
    Function.Injective (appendMiddlePath G Q (x := x) (t := t)) := by
  rintro ⟨y, p⟩ ⟨z, q⟩ h
  change p.cons (WordPath.reverseArrow G Q y.2) =
    q.cons (WordPath.reverseArrow G Q z.2) at h
  have hyzVertex : WordPath.vertex G Q y.1 = WordPath.vertex G Q z.1 :=
    Quiver.Path.obj_eq_of_cons_eq_cons h
  have hyz : y.1 = z.1 :=
    congrArg WordPath.ReverseWordQuiver.pos hyzVertex
  have hyzSubtype : y = z := Subtype.ext hyz
  subst z
  have hpq : p = q :=
    eq_of_heq (Quiver.Path.heq_of_cons_eq_cons h)
  subst q
  rfl

/-- The total final-edge operation as an embedding. -/
def appendMiddlePathEmbedding
    (G : SimpleGraph L) (Q : List L)
    (x t : Fin Q.length) :
    (Σ y : {y : Fin Q.length // IsMiddle G Q x y},
      Quiver.Path (WordPath.vertex G Q t) (WordPath.vertex G Q y.1)) ↪
      Quiver.Path (WordPath.vertex G Q t) (WordPath.vertex G Q x) :=
  ⟨appendMiddlePath G Q, appendMiddlePath_injective G Q x t⟩

/-- The outgoing-arrow map in the free word-path category. -/
def pathOutgoingMap
    (G : SimpleGraph L) (Q : List L)
    (x t : Fin Q.length) :
    ((y : {y : Fin Q.length // IsMiddle G Q x y}) →
      (WordPath.obj K G Q y.1 ⟶ WordPath.obj K G Q t)) →ₗ[K]
      (WordPath.obj K G Q x ⟶ WordPath.obj K G Q t) where
  toFun g := ∑ y, WordPath.middleArrow (K := K) G Q y.2 ≫ g y
  map_add' := by
    intro f g
    simp only [Pi.add_apply, Preadditive.comp_add, Finset.sum_add_distrib]
  map_smul' := by
    intro k f
    simp only [Pi.smul_apply, Linear.comp_smul, Finset.smul_sum,
      RingHom.id_apply]

/-- The product path basis on the domain of the free outgoing-arrow map. -/
def pathOutgoingBasis
    (G : SimpleGraph L) (Q : List L)
    (x t : Fin Q.length) :
    Module.Basis
      (Σ y : {y : Fin Q.length // IsMiddle G Q x y},
        Quiver.Path (WordPath.vertex G Q t) (WordPath.vertex G Q y.1)) K
      ((y : {y : Fin Q.length // IsMiddle G Q x y}) →
        (WordPath.obj K G Q y.1 ⟶ WordPath.obj K G Q t)) :=
  Pi.basis fun y ↦ WordPath.homPathBasis G Q
    (WordPath.obj K G Q y.1) (WordPath.obj K G Q t)

/-- Each product-basis vector is sent to the corresponding path with its
final reverse edge appended. -/
theorem pathOutgoingMap_basis
    (G : SimpleGraph L) (Q : List L)
    (x t : Fin Q.length)
    (s : Σ y : {y : Fin Q.length // IsMiddle G Q x y},
      Quiver.Path (WordPath.vertex G Q t) (WordPath.vertex G Q y.1)) :
    pathOutgoingMap (K := K) G Q x t
        (pathOutgoingBasis (K := K) G Q x t s) =
      WordPath.pathHom G Q (appendMiddlePath G Q s) := by
  classical
  rcases s with ⟨y, p⟩
  rw [show pathOutgoingBasis (K := K) G Q x t ⟨y, p⟩ =
      Pi.single y (WordPath.homPathBasis G Q
        (WordPath.obj K G Q y.1) (WordPath.obj K G Q t) p) by
    exact Pi.basis_apply _ _]
  let d : (z : {z : Fin Q.length // IsMiddle G Q x z}) →
      (WordPath.obj K G Q z.1 ⟶ WordPath.obj K G Q t) :=
    Pi.single y (WordPath.homPathBasis G Q
      (WordPath.obj K G Q y.1) (WordPath.obj K G Q t) p)
  change (∑ z, WordPath.middleArrow (K := K) G Q z.2 ≫ d z) = _
  rw [Finset.sum_eq_single y]
  · simp [d, homPathBasis_apply, appendMiddlePath, WordPath.middleArrow,
      WordPath.pathHom_comp]
    rfl
  · intro z _ hzy
    simp [d, hzy]
  · intro hy
    exact (hy (Finset.mem_univ y)).elim

/-- The free outgoing-arrow map is injective: reverse paths have a unique
final edge, equivalently original paths have a unique first arrow. -/
theorem pathOutgoingMap_injective
    (G : SimpleGraph L) (Q : List L)
    (x t : Fin Q.length) :
    Function.Injective (pathOutgoingMap (K := K) G Q x t) := by
  apply LinearMap.injective_of_linearIndependent
    (pathOutgoingBasis (K := K) G Q x t).span_eq
  have hli := (WordPath.homPathBasis G Q
    (WordPath.obj K G Q x) (WordPath.obj K G Q t)).linearIndependent.comp
      (appendMiddlePathEmbedding G Q x t)
      (appendMiddlePathEmbedding G Q x t).injective
  change LinearIndependent K (fun s ↦
    pathOutgoingMap (K := K) G Q x t
      (pathOutgoingBasis (K := K) G Q x t s))
  have hfamily :
      (fun s ↦ pathOutgoingMap (K := K) G Q x t
        (pathOutgoingBasis (K := K) G Q x t s)) =
      (fun s ↦ WordPath.homPathBasis G Q
        (WordPath.obj K G Q x) (WordPath.obj K G Q t)
        (appendMiddlePath G Q s)) := by
    funext s
    rw [pathOutgoingMap_basis, homPathBasis_apply]
    rfl
  rw [hfamily]
  change LinearIndependent K (fun s ↦ WordPath.homPathBasis G Q
    (WordPath.obj K G Q x) (WordPath.obj K G Q t)
    ((appendMiddlePathEmbedding G Q x t) s)) at hli
  change LinearIndependent K (fun s ↦ WordPath.homPathBasis G Q
    (WordPath.obj K G Q x) (WordPath.obj K G Q t)
    ((appendMiddlePathEmbedding G Q x t) s))
  exact hli

/-! ## The outgoing-middle-to-next-occurrence map -/

/-- For a next occurrence `b` of the label at `x`, outgoing middle vertices
at `x` are canonically the incoming middle vertices at `b`. -/
def outgoingMiddleEquivIncoming
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    {x b : Fin Q.length} (hxb : IsPrevious Q x b) :
    {y : Fin Q.length // IsMiddle G Q x y} ≃
      {y : Fin Q.length // IsMiddle G Q y b} where
  toFun y := ⟨y.1,
    (isMiddle_iff_previous_isMiddle hAlt hxb y.1).mpr y.2⟩
  invFun y := ⟨y.1,
    (isMiddle_iff_previous_isMiddle hAlt hxb y.1).mp y.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- The second arrow `y → b` of the mesh beginning at `x`, expressed using
an outgoing middle witness `x → y`. -/
def pathMiddleNextArrow
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    {x y b : Fin Q.length}
    (hxb : IsPrevious Q x b) (hxy : IsMiddle G Q x y) :
    WordPath.obj K G Q y ⟶ WordPath.obj K G Q b :=
  WordPath.middleArrow (K := K) G Q
    ((isMiddle_iff_previous_isMiddle hAlt hxb y).mpr hxy)

/-- Reindex a mesh relation at the next occurrence by the outgoing middle
vertices at its predecessor. -/
theorem meshRelation_eq_sum_outgoing
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    {x b : Fin Q.length} (hxb : IsPrevious Q x b) :
    WordPath.meshRelation (K := K) G Q hAlt hxb =
      ∑ y : {y : Fin Q.length // IsMiddle G Q x y},
        WordPath.middleArrow (K := K) G Q y.2 ≫
          pathMiddleNextArrow (K := K) G Q hAlt hxb y.2 := by
  rw [WordPath.meshRelation]
  apply Fintype.sum_equiv (outgoingMiddleEquivIncoming G Q hAlt hxb).symm
  intro y
  rfl

/-- Evaluation of the second mesh map, from the next occurrence(s) to the
outgoing middle vertices, in the free path category. -/
def pathNextMap
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    (x t : Fin Q.length) :
    ((b : {b : Fin Q.length // IsPrevious Q x b}) →
      (WordPath.obj K G Q b.1 ⟶ WordPath.obj K G Q t)) →ₗ[K]
      ((y : {y : Fin Q.length // IsMiddle G Q x y}) →
        (WordPath.obj K G Q y.1 ⟶ WordPath.obj K G Q t)) where
  toFun a y := ∑ b,
    pathMiddleNextArrow (K := K) G Q hAlt b.2 y.2 ≫ a b
  map_add' := by
    intro a b
    funext y
    simp only [Pi.add_apply, Preadditive.comp_add, Finset.sum_add_distrib]
  map_smul' := by
    intro k a
    funext y
    simp only [Pi.smul_apply, Linear.comp_smul, Finset.smul_sum,
      RingHom.id_apply]

/-- The two evaluated free mesh maps compose to the sum of right multiples
of the mesh relations beginning at `x`. -/
theorem pathOutgoingMap_nextMap
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    (x t : Fin Q.length)
    (a : (b : {b : Fin Q.length // IsPrevious Q x b}) →
      (WordPath.obj K G Q b.1 ⟶ WordPath.obj K G Q t)) :
    pathOutgoingMap (K := K) G Q x t
        (pathNextMap (K := K) G Q hAlt x t a) =
      ∑ b, WordPath.meshRelation (K := K) G Q hAlt b.2 ≫ a b := by
  classical
  change (∑ y, WordPath.middleArrow (K := K) G Q y.2 ≫
      (∑ b, pathMiddleNextArrow (K := K) G Q hAlt b.2 y.2 ≫ a b)) = _
  simp only [Preadditive.comp_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  rw [meshRelation_eq_sum_outgoing, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro y hy
  rfl

/-- The second arrow `y → b` of a mesh beginning at `x`, in the quotient
category. -/
def quotientMiddleNextArrow
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    {x y b : Fin Q.length}
    (hxb : IsPrevious Q x b) (hxy : IsMiddle G Q x y) :
    WordMesh.obj (K := K) G Q hAlt y ⟶
      WordMesh.obj (K := K) G Q hAlt b :=
  WordMesh.quotientHom (K := K) G Q hAlt
    (pathMiddleNextArrow (K := K) G Q hAlt hxb hxy)

/-- Evaluation of the second mesh map, from next occurrences to outgoing
middle vertices, in the mesh quotient. -/
def quotientNextMap
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    (x t : Fin Q.length) :
    ((b : {b : Fin Q.length // IsPrevious Q x b}) →
      (WordMesh.obj (K := K) G Q hAlt b.1 ⟶
        WordMesh.obj (K := K) G Q hAlt t)) →ₗ[K]
      ((y : {y : Fin Q.length // IsMiddle G Q x y}) →
        (WordMesh.obj (K := K) G Q hAlt y.1 ⟶
          WordMesh.obj (K := K) G Q hAlt t)) where
  toFun a y := ∑ b,
    quotientMiddleNextArrow (K := K) G Q hAlt b.2 y.2 ≫ a b
  map_add' := by
    intro a b
    funext y
    simp only [Pi.add_apply, Preadditive.comp_add, Finset.sum_add_distrib]
  map_smul' := by
    intro k a
    funext y
    simp only [Pi.smul_apply, Linear.comp_smul, Finset.smul_sum,
      RingHom.id_apply]

/-- Quotienting commutes with the evaluated outgoing-arrow map. -/
theorem quotientHom_pathOutgoingMap
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    (x t : Fin Q.length)
    (g : (y : {y : Fin Q.length // IsMiddle G Q x y}) →
      (WordPath.obj K G Q y.1 ⟶ WordPath.obj K G Q t)) :
    WordMesh.quotientHom (K := K) G Q hAlt
        (pathOutgoingMap (K := K) G Q x t g) =
      quotientOutgoingMap (K := K) G Q hAlt x t
        (fun y ↦ WordMesh.quotientHom (K := K) G Q hAlt (g y)) := by
  change WordMesh.quotientHomLinearMap (K := K) G Q hAlt x t
      (∑ y, WordPath.middleArrow (K := K) G Q y.2 ≫ g y) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro y hy
  change WordMesh.quotientHom (K := K) G Q hAlt
    (WordPath.middleArrow (K := K) G Q y.2 ≫ g y) = _
  rw [WordMesh.quotientHom_comp]
  rfl

/-- Quotienting commutes pointwise with the next-occurrence map. -/
theorem quotientHom_pathNextMap
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    (x t : Fin Q.length)
    (a : (b : {b : Fin Q.length // IsPrevious Q x b}) →
      (WordPath.obj K G Q b.1 ⟶ WordPath.obj K G Q t)) :
    (fun y ↦ WordMesh.quotientHom (K := K) G Q hAlt
        (pathNextMap (K := K) G Q hAlt x t a y)) =
      quotientNextMap (K := K) G Q hAlt x t
        (fun b ↦ WordMesh.quotientHom (K := K) G Q hAlt (a b)) := by
  funext y
  change WordMesh.quotientHomLinearMap (K := K) G Q hAlt y.1 t
      (∑ b, pathMiddleNextArrow (K := K) G Q hAlt b.2 y.2 ≫ a b) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro b hb
  change WordMesh.quotientHom (K := K) G Q hAlt
    (pathMiddleNextArrow (K := K) G Q hAlt b.2 y.2 ≫ a b) = _
  rw [WordMesh.quotientHom_comp]
  rfl

/-- The evaluated next-occurrence and outgoing maps compose to zero in the
mesh quotient. -/
theorem quotientOutgoingMap_nextMap_eq_zero
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    (x t : Fin Q.length)
    (a : (b : {b : Fin Q.length // IsPrevious Q x b}) →
      (WordMesh.obj (K := K) G Q hAlt b.1 ⟶
        WordMesh.obj (K := K) G Q hAlt t)) :
    quotientOutgoingMap (K := K) G Q hAlt x t
      (quotientNextMap (K := K) G Q hAlt x t a) = 0 := by
  classical
  let w : (b : {b : Fin Q.length // IsPrevious Q x b}) →
      (WordPath.obj K G Q b.1 ⟶ WordPath.obj K G Q t) :=
    fun b ↦ Classical.choose
      (WordMesh.quotientHom_surjective (K := K) G Q hAlt b.1 t (a b))
  have hw : ∀ b, WordMesh.quotientHom (K := K) G Q hAlt (w b) = a b :=
    fun b ↦ Classical.choose_spec
      (WordMesh.quotientHom_surjective (K := K) G Q hAlt b.1 t (a b))
  have ha : a = fun b ↦ WordMesh.quotientHom (K := K) G Q hAlt (w b) := by
    funext b
    exact (hw b).symm
  rw [ha]
  rw [← quotientHom_pathNextMap]
  rw [← quotientHom_pathOutgoingMap]
  rw [pathOutgoingMap_nextMap]
  apply (quotientHom_eq_zero_iff
    (K := K) G Q hAlt _).mpr
  apply (WordMesh.meshIdeal (K := K) G Q hAlt).hom _ _ |>.sum_mem
  intro b hb
  exact (WordMesh.meshIdeal (K := K) G Q hAlt).postcomp (w b)
    (HomIdeal.relation_mem_linearSpan
      (WordMesh.meshGeneratorSet (K := K) G Q hAlt)
      (show WordPath.meshRelation (K := K) G Q hAlt b.2 ∈
        WordMesh.meshGeneratorSet (K := K) G Q hAlt
          (WordPath.obj K G Q x) (WordPath.obj K G Q b.1) from
        ⟨b.2, rfl⟩))

/-- Exactness at the outgoing-middle term after evaluation against a fixed
target. The proof combines the source ideal recurrence with freeness of the
outgoing-arrow map before quotienting. -/
theorem quotient_exact_at_outgoing_middle
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    (x t : Fin Q.length) :
    Function.Exact
      (quotientNextMap (K := K) G Q hAlt x t)
      (quotientOutgoingMap (K := K) G Q hAlt x t) := by
  classical
  intro v
  constructor
  · intro hv
    let w : (y : {y : Fin Q.length // IsMiddle G Q x y}) →
        (WordPath.obj K G Q y.1 ⟶ WordPath.obj K G Q t) :=
      fun y ↦ Classical.choose
        (WordMesh.quotientHom_surjective (K := K) G Q hAlt y.1 t (v y))
    have hw : ∀ y, WordMesh.quotientHom (K := K) G Q hAlt (w y) = v y :=
      fun y ↦ Classical.choose_spec
        (WordMesh.quotientHom_surjective (K := K) G Q hAlt y.1 t (v y))
    have hq : WordMesh.quotientHom (K := K) G Q hAlt
        (pathOutgoingMap (K := K) G Q x t w) = 0 := by
      rw [quotientHom_pathOutgoingMap]
      have hwfun :
          (fun y ↦ WordMesh.quotientHom (K := K) G Q hAlt (w y)) = v := by
        funext y
        exact hw y
      rw [hwfun, hv]
    have hIdeal := (quotientHom_eq_zero_iff
      (K := K) G Q hAlt
      (pathOutgoingMap (K := K) G Q x t w)).mp hq
    obtain ⟨a, g, hg, hnormal⟩ :=
      (mem_meshIdeal_iff_hasStartingNormalForm (K := K) G Q hAlt x t
        (pathOutgoingMap (K := K) G Q x t w)).mp hIdeal
    have hPath : w = pathNextMap (K := K) G Q hAlt x t a + g := by
      apply pathOutgoingMap_injective (K := K) G Q x t
      rw [map_add, pathOutgoingMap_nextMap]
      change pathOutgoingMap (K := K) G Q x t w =
        (∑ b, WordPath.meshRelation (K := K) G Q hAlt b.2 ≫ a b) +
          ∑ y, WordPath.middleArrow (K := K) G Q y.2 ≫ g y
      exact hnormal
    refine ⟨fun b ↦ WordMesh.quotientHom (K := K) G Q hAlt (a b), ?_⟩
    funext y
    have hnext := congrFun (quotientHom_pathNextMap
      (K := K) G Q hAlt x t a) y
    have hwy := congrFun hPath y
    have hwy' : w y =
        pathNextMap (K := K) G Q hAlt x t a y + g y := by
      simpa only [Pi.add_apply] using hwy
    rw [← hnext, ← hw y, hwy', WordMesh.quotientHom_add]
    have hgy : WordMesh.quotientHom (K := K) G Q hAlt (g y) = 0 :=
      (quotientHom_eq_zero_iff
        (K := K) G Q hAlt (g y)).mpr (hg y)
    rw [hgy, add_zero]
  · rintro ⟨a, rfl⟩
    exact quotientOutgoingMap_nextMap_eq_zero G Q hAlt x t a

end QuotientSubmoduleEquidistribution.RepresentationDirected.IyamaMesh.WordMeshStartingExactness
