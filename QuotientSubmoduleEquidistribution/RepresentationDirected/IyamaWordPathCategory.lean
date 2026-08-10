import QuotientSubmoduleEquidistribution.Foundation.RepresentationTheory.Quiver.Representation.Projective.Acyclic
import QuotientSubmoduleEquidistribution.Foundation.RepresentationTheory.Quiver.Acyclic.FinitePaths
import QuotientSubmoduleEquidistribution.RepresentationDirected.ARWordCombinatorics

/-!
# The finite linear word-path category and its mesh generators

This file constructs the free linear category on the word quiver through
The project foundation's representable projectives.  The auxiliary quiver is reversed so
that morphisms between projectives point in the word's original direction.
It also defines the ordinary finite mesh relation at every repeated position.

No concrete algebra, quiver instance, or module classification is used.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open CategoryTheory
open QuotientSubmoduleEquidistribution.Foundation

namespace QuotientSubmoduleEquidistribution.RepresentationDirected.IyamaMesh.WordPath

open QuotientSubmoduleEquidistribution.RepresentationDirected.ARWord

universe uK uL

variable {K : Type uK} [Field K]
variable {L : Type uL}

/-- The reverse of the word quiver.  Reversal makes the project foundation's projective
representatives have morphisms in the manuscript's original orientation. -/
@[ext]
structure ReverseWordQuiver (G : SimpleGraph L) (Q : List L) where
  pos : Fin Q.length
deriving DecidableEq

/-- Reverse-word vertices are equivalent to word positions. -/
def reverseWordQuiverEquivFin (G : SimpleGraph L) (Q : List L) :
    ReverseWordQuiver G Q ≃ Fin Q.length where
  toFun := ReverseWordQuiver.pos
  invFun := ReverseWordQuiver.mk
  left_inv x := by cases x; rfl
  right_inv _ := rfl

instance (G : SimpleGraph L) (Q : List L) :
    Fintype (ReverseWordQuiver G Q) :=
  Fintype.ofEquiv (Fin Q.length) (reverseWordQuiverEquivFin G Q).symm

instance (G : SimpleGraph L) (Q : List L) :
    Quiver (ReverseWordQuiver G Q) where
  Hom x y := PLift (IsMiddle G Q y.pos x.pos)

/-- There is at most one reverse-word arrow between two fixed positions. -/
instance (G : SimpleGraph L) (Q : List L)
    (x y : ReverseWordQuiver G Q) : Finite (x ⟶ y) := by
  letI : Subsingleton (x ⟶ y) :=
    ⟨fun a b ↦ by cases a; cases b; congr⟩
  exact Finite.of_subsingleton

/-- Every reverse-word arrow strictly decreases its position. -/
theorem hom_lt (G : SimpleGraph L) (Q : List L)
    {x y : ReverseWordQuiver G Q} (e : x ⟶ y) : y.pos < x.pos :=
  e.down.2.1

/-- Every reverse-word path weakly decreases its position. -/
theorem path_le (G : SimpleGraph L) (Q : List L) :
    ∀ {x y : ReverseWordQuiver G Q},
      Quiver.Path x y → y.pos ≤ x.pos := by
  intro x y p
  induction p with
  | nil => exact le_rfl
  | cons p e ih => exact (hom_lt G Q e).le.trans ih

/-- The reverse word quiver is acyclic. -/
theorem isAcyclic (G : SimpleGraph L) (Q : List L) :
    Quiver.IsAcyclic (ReverseWordQuiver G Q) := by
  intro x p
  cases p with
  | nil => rfl
  | cons p e =>
      exact False.elim
        ((not_lt_of_ge (path_le G Q p)) (hom_lt G Q e))

/-- Every fixed-endpoint reverse-word path type is finite. -/
instance finitePath (G : SimpleGraph L) (Q : List L)
    (x y : ReverseWordQuiver G Q) : Finite (Quiver.Path x y) := by
  letI : Finite
      (Σ a b : ReverseWordQuiver G Q, Quiver.Path a b) :=
    finite_paths_of_isAcyclic (isAcyclic G Q)
  let inner : Quiver.Path x y ↪
      (Σ b : ReverseWordQuiver G Q, Quiver.Path x b) :=
    Function.Embedding.sigmaMk
      (β := fun b : ReverseWordQuiver G Q ↦ Quiver.Path x b) y
  let outer : (Σ b : ReverseWordQuiver G Q, Quiver.Path x b) ↪
      (Σ a b : ReverseWordQuiver G Q, Quiver.Path a b) :=
    Function.Embedding.sigmaMk
      (β := fun a : ReverseWordQuiver G Q ↦
        Σ b : ReverseWordQuiver G Q, Quiver.Path a b) x
  exact Finite.of_injective (fun p ↦ outer (inner p))
    (outer.injective.comp inner.injective)

/-- A word position regarded as a vertex of the reverse word quiver. -/
def vertex (G : SimpleGraph L) (Q : List L) (x : Fin Q.length) :
    ReverseWordQuiver G Q :=
  ⟨x⟩

/-- The full linear subcategory of reverse-word-quiver representations on the
indecomposable representable projectives. -/
abbrev Category (K : Type uK) [Field K]
    (G : SimpleGraph L) (Q : List L) :=
  InducedCategory
    (QuiverRep K (ReverseWordQuiver G Q))
    (fun x : Fin Q.length ↦
      indecProjRep K (ReverseWordQuiver G Q) (vertex G Q x))

/-- The underlying word position of an object of the path category. -/
def position (G : SimpleGraph L) (Q : List L)
    (x : Category K G Q) : Fin Q.length :=
  x

/-- A position with the path-category structure made explicit. -/
def obj (K : Type uK) [Field K]
    (G : SimpleGraph L) (Q : List L) (x : Fin Q.length) :
    Category K G Q :=
  x

/-- Morphisms between word vertices are the finite linear combinations of
reverse-quiver paths in the opposite direction. -/
def homPathLinearEquiv (G : SimpleGraph L) (Q : List L)
    (x y : Category K G Q) :
    (x ⟶ y) ≃ₗ[K]
      (Quiver.Path (vertex G Q y) (vertex G Q x) →₀ K) :=
  InducedCategory.homLinearEquiv.trans
    ((indecProjRepHomEquiv (vertex G Q x)
      (indecProjRep K (ReverseWordQuiver G Q) (vertex G Q y))).trans
      (indecProjRepBasis K (vertex G Q y) (vertex G Q x)).repr)

/-- The morphism represented by one reverse-quiver path. -/
def pathHom (G : SimpleGraph L) (Q : List L)
    {x y : Category K G Q}
    (p : Quiver.Path (vertex G Q y) (vertex G Q x)) :
    x ⟶ y :=
  (homPathLinearEquiv G Q x y).symm (Finsupp.single p 1)

/-- Reverse-quiver paths form a basis of every Hom space. -/
def homPathBasis (G : SimpleGraph L) (Q : List L)
    (x y : Category K G Q) :
    Module.Basis
      (Quiver.Path (vertex G Q y) (vertex G Q x)) K
      (x ⟶ y) :=
  Finsupp.basisSingleOne.map (homPathLinearEquiv G Q x y).symm

/-- Hom spaces in the finite acyclic path category are finite-dimensional. -/
instance homModuleFinite (G : SimpleGraph L) (Q : List L)
    (x y : Category K G Q) : Module.Finite K (x ⟶ y) :=
  Module.Finite.of_basis (homPathBasis G Q x y)

@[simp]
theorem homPathLinearEquiv_pathHom (G : SimpleGraph L) (Q : List L)
    {x y : Category K G Q}
    (p : Quiver.Path (vertex G Q y) (vertex G Q x)) :
    homPathLinearEquiv G Q x y (pathHom G Q p) = Finsupp.single p 1 :=
  (homPathLinearEquiv G Q x y).apply_symm_apply _

@[simp]
theorem homPathLinearEquiv_id (G : SimpleGraph L) (Q : List L)
    (x : Category K G Q) :
    homPathLinearEquiv G Q x x (𝟙 x) =
      Finsupp.single Quiver.Path.nil 1 := by
  change
    (indecProjRepBasis K (vertex G Q x) (vertex G Q x)).repr
        (((𝟙 (indecProjRep K (ReverseWordQuiver G Q) (vertex G Q x)) :
            indecProjRep K (ReverseWordQuiver G Q) (vertex G Q x) ⟶
              indecProjRep K (ReverseWordQuiver G Q) (vertex G Q x))).app
          (vertex G Q x)
          (indecProjRepBasis K (vertex G Q x) (vertex G Q x)
            Quiver.Path.nil)) =
      Finsupp.single Quiver.Path.nil 1
  simp

@[simp]
theorem pathHom_nil (G : SimpleGraph L) (Q : List L)
    (x : Category K G Q) :
    pathHom G Q (Quiver.Path.nil :
      Quiver.Path (vertex G Q x) (vertex G Q x)) = 𝟙 x := by
  apply (homPathLinearEquiv G Q x x).injective
  simp

/-- The underlying natural transformation of a path-basis morphism. -/
theorem pathHom_hom (G : SimpleGraph L) (Q : List L)
    {x y : Category K G Q}
    (p : Quiver.Path (vertex G Q y) (vertex G Q x)) :
    (pathHom G Q p).hom =
      indecProjRepHom
        (vertex G Q x)
        (indecProjRep K (ReverseWordQuiver G Q) (vertex G Q y))
        (indecProjRepBasis K (vertex G Q y) (vertex G Q x) p) := by
  apply (indecProjRepHomEquiv
    (vertex G Q x)
    (indecProjRep K (ReverseWordQuiver G Q) (vertex G Q y))).injective
  apply (indecProjRepBasis K (vertex G Q y) (vertex G Q x)).repr.injective
  change homPathLinearEquiv G Q x y (pathHom G Q p) = _
  simp

@[simp, reassoc]
theorem pathHom_comp (G : SimpleGraph L) (Q : List L)
    {x y z : Category K G Q}
    (p : Quiver.Path (vertex G Q y) (vertex G Q x))
    (q : Quiver.Path (vertex G Q z) (vertex G Q y)) :
    pathHom G Q p ≫ pathHom G Q q = pathHom G Q (q.comp p) := by
  apply (homPathLinearEquiv G Q x z).injective
  simp only [homPathLinearEquiv_pathHom]
  simp [homPathLinearEquiv, pathHom]

/-- Morphisms can point only weakly forward in the original word order. -/
theorem hom_eq_zero_of_not_le (G : SimpleGraph L) (Q : List L)
    {x y : Category K G Q}
    (hxy : ¬ position G Q x ≤ position G Q y) (f : x ⟶ y) :
    f = 0 := by
  apply (homPathLinearEquiv G Q x y).injective
  ext p
  exact False.elim (hxy (path_le G Q p))

/-- In particular, every strictly backward morphism vanishes. -/
theorem hom_eq_zero_of_lt (G : SimpleGraph L) (Q : List L)
    {x y : Category K G Q}
    (hyx : position G Q y < position G Q x) (f : x ⟶ y) :
    f = 0 :=
  hom_eq_zero_of_not_le G Q (not_le_of_gt hyx) f

/-- Evaluation at the trivial path identifies a vertex endomorphism space
with the coefficient field. -/
def selfHomLinearEquiv (G : SimpleGraph L) (Q : List L)
    (x : Fin Q.length) :
    (obj K G Q x ⟶ obj K G Q x) ≃ₗ[K] K :=
  (homPathLinearEquiv G Q (obj K G Q x) (obj K G Q x)).trans
    { toFun := fun f ↦ f Quiver.Path.nil
      invFun := fun k ↦ Finsupp.single Quiver.Path.nil k
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      left_inv := by
        intro f
        ext p
        have hp : p = Quiver.Path.nil := isAcyclic G Q p
        subst p
        simp
      right_inv := fun _ ↦ Finsupp.single_eq_same }

@[simp]
theorem selfHomLinearEquiv_id (G : SimpleGraph L) (Q : List L)
    (x : Fin Q.length) :
    selfHomLinearEquiv (K := K) G Q x (𝟙 (obj K G Q x)) = 1 := by
  change
    (homPathLinearEquiv G Q (obj K G Q x) (obj K G Q x)
      (𝟙 (obj K G Q x))) Quiver.Path.nil = 1
  rw [homPathLinearEquiv_id]
  exact Finsupp.single_eq_same

/-- Every endomorphism of a path-category vertex is its trivial-path
coefficient times the identity. -/
theorem eq_smul_id_selfHomLinearEquiv (G : SimpleGraph L) (Q : List L)
    (x : Fin Q.length) (f : obj K G Q x ⟶ obj K G Q x) :
    f = selfHomLinearEquiv (K := K) G Q x f • 𝟙 (obj K G Q x) := by
  apply (selfHomLinearEquiv (K := K) G Q x).injective
  rw [LinearEquiv.map_smul, selfHomLinearEquiv_id, smul_eq_mul, mul_one]

/-- The middle positions at an endpoint form a finite type. -/
noncomputable instance middleFintype (G : SimpleGraph L) (Q : List L)
    (x : Fin Q.length) :
    Fintype {y : Fin Q.length // IsMiddle G Q y x} :=
  Fintype.ofFinite _

/-- The reverse-quiver arrow corresponding to a word-mesh arrow `y → x`. -/
def reverseArrow (G : SimpleGraph L) (Q : List L)
    {y x : Fin Q.length} (h : IsMiddle G Q y x) :
    vertex G Q x ⟶ vertex G Q y :=
  PLift.up h

/-- The one-arrow reverse-quiver path corresponding to `y → x`. -/
def reverseArrowPath (G : SimpleGraph L) (Q : List L)
    {y x : Fin Q.length} (h : IsMiddle G Q y x) :
    Quiver.Path (vertex G Q x) (vertex G Q y) :=
  (reverseArrow G Q h).toPath

/-- The basis morphism associated to a middle arrow. -/
def middleArrow (G : SimpleGraph L) (Q : List L)
    {y x : Fin Q.length} (h : IsMiddle G Q y x) :
    obj K G Q y ⟶ obj K G Q x :=
  pathHom G Q (reverseArrowPath G Q h)

/-- The reverse-quiver length-two path contributed by an intermediate vertex
to the mesh at a repeated word position. -/
def meshPath (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    {p x : Fin Q.length} (hpx : IsPrevious Q p x)
    (y : {y : Fin Q.length // IsMiddle G Q y x}) :
    Quiver.Path (vertex G Q x) (vertex G Q p) :=
  (reverseArrowPath G Q y.2).comp
    (reverseArrowPath G Q
      ((isMiddle_iff_previous_isMiddle hAlt hpx y.1).mp y.2))

/-- The ordinary finite mesh relation at a repeated word position. -/
def meshRelation (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    {p x : Fin Q.length} (hpx : IsPrevious Q p x) :
    obj K G Q p ⟶ obj K G Q x :=
  ∑ y : {y : Fin Q.length // IsMiddle G Q y x},
    middleArrow G Q
        ((isMiddle_iff_previous_isMiddle hAlt hpx y.1).mp y.2) ≫
      middleArrow G Q y.2

/-- Path coordinates of a mesh relation are its length-two mesh paths. -/
theorem homPathLinearEquiv_meshRelation
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    {p x : Fin Q.length} (hpx : IsPrevious Q p x) :
    homPathLinearEquiv G Q (obj K G Q p) (obj K G Q x)
        (meshRelation (K := K) G Q hAlt hpx) =
      ∑ y : {y : Fin Q.length // IsMiddle G Q y x},
        Finsupp.single (meshPath G Q hAlt hpx y) 1 := by
  rw [meshRelation, map_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [middleArrow, middleArrow, pathHom_comp,
    homPathLinearEquiv_pathHom]
  rfl

end QuotientSubmoduleEquidistribution.RepresentationDirected.IyamaMesh.WordPath
