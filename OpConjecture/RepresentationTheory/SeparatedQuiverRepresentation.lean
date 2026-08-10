import OpConjecture.RepresentationTheory.SeparatedQuiver
import OpConjecture.Foundation.RepresentationTheory.Quiver.Representation.Basic
import Mathlib.CategoryTheory.PathCategory.MorphismProperty

/-!
# Coordinate data for representations of a separated quiver
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace OpConjecture.SeparatedQuiver

universe uK uV v w

variable (K : Type uK) (V : Type uV)
variable [Field K] [Quiver.{v} V]

/-- Vertex spaces and arrow maps for the bipartite separated quiver. -/
structure RepresentationData where
  plus : V → ModuleCat.{w} K
  minus : V → ModuleCat.{w} K
  arrow : ∀ {i j : V}, (i ⟶ j) → (plus i ⟶ minus j)

namespace RepresentationData

variable {K V}

/-- A morphism of separated-quiver coordinate data. -/
structure Hom (D E : RepresentationData.{uK, uV, v, w} K V) where
  plus : ∀ i, D.plus i ⟶ E.plus i
  minus : ∀ i, D.minus i ⟶ E.minus i
  comm : ∀ {i j : V} (e : i ⟶ j),
    D.arrow e ≫ minus j = plus i ≫ E.arrow e

@[ext]
theorem Hom.ext {D E : RepresentationData.{uK, uV, v, w} K V}
    {f g : Hom D E} (hplus : f.plus = g.plus)
    (hminus : f.minus = g.minus) : f = g := by
  cases f
  cases g
  simp_all

instance category :
    Category (RepresentationData.{uK, uV, v, w} K V) where
  Hom := Hom
  id D :=
    { plus := fun _ ↦ 𝟙 _
      minus := fun _ ↦ 𝟙 _
      comm := by simp }
  comp f g :=
    { plus := fun i ↦ f.plus i ≫ g.plus i
      minus := fun i ↦ f.minus i ≫ g.minus i
      comm := by
        intro i j e
        rw [← Category.assoc, f.comm e, Category.assoc,
          g.comm e, ← Category.assoc] }
  assoc := by intros; ext <;> rfl
  id_comp := by intros; ext <;> simp
  comp_id := by intros; ext <;> simp

/-- Coordinate data as a prefunctor on the arrows of the separated quiver. -/
def toPrefunctor
    (D : RepresentationData.{uK, uV, v, w} K V) :
    Vertex V ⥤q ModuleCat.{w} K where
  obj
    | Sum.inl i => D.plus i
    | Sum.inr i => D.minus i
  map {a b} e := by
    cases a with
    | inl i =>
        cases b with
        | inl j => exact PEmpty.elim e
        | inr j => exact D.arrow e
    | inr i =>
        cases b with
        | inl j => exact PEmpty.elim e
        | inr j => exact PEmpty.elim e

/-- Coordinate data determine a representation of the separated quiver. -/
def toQuiverRep
    (D : RepresentationData.{uK, uV, v, w} K V) :
    OpConjecture.Foundation.QuiverRep K (Vertex V) :=
  CategoryTheory.Paths.lift D.toPrefunctor

@[simp]
theorem toQuiverRep_obj_plus
    (D : RepresentationData.{uK, uV, v, w} K V) (i : V) :
    D.toQuiverRep.obj (Sum.inl i) = D.plus i := rfl

@[simp]
theorem toQuiverRep_obj_minus
    (D : RepresentationData.{uK, uV, v, w} K V) (i : V) :
    D.toQuiverRep.obj (Sum.inr i) = D.minus i := rfl

@[simp]
theorem toQuiverRep_map_arrow
    (D : RepresentationData.{uK, uV, v, w} K V)
    {i j : V} (e : i ⟶ j) :
    D.toQuiverRep.map
        (Quiver.Hom.toPath
          (show (Sum.inl i : Vertex V) ⟶ Sum.inr j from e)) =
      D.arrow e := by
  simp [toQuiverRep, toPrefunctor]

/-- A coordinate morphism induces a natural transformation of quiver
representations. -/
def toQuiverRepMap
    {D E : RepresentationData.{uK, uV, v, w} K V} (f : D ⟶ E) :
    D.toQuiverRep ⟶ E.toQuiverRep :=
  CategoryTheory.Paths.liftNatTrans
    (fun x ↦ match x with
      | Sum.inl i => f.plus i
      | Sum.inr i => f.minus i)
    (by
      intro a b e
      cases a with
      | inl i =>
          cases b with
          | inl j => exact PEmpty.elim e
          | inr j =>
              simpa only [toQuiverRep_obj_plus, toQuiverRep_obj_minus,
                toQuiverRep_map_arrow] using f.comm e
      | inr i =>
          cases b with
          | inl j => exact PEmpty.elim e
          | inr j => exact PEmpty.elim e)

/-- The functor from coordinate data to separated-quiver representations. -/
def toQuiverRepFunctor :
    RepresentationData.{uK, uV, v, w} K V ⥤
      OpConjecture.Foundation.QuiverRep K (Vertex V) where
  obj := toQuiverRep
  map := toQuiverRepMap
  map_id D := by
    ext x
    cases x <;> rfl
  map_comp f g := by
    ext x
    cases x <;> rfl

/-- Restrict a separated-quiver representation to its vertex spaces and
length-one arrow maps. -/
def ofQuiverRep (M : OpConjecture.Foundation.QuiverRep K (Vertex V)) :
    RepresentationData.{uK, uV, v, w} K V where
  plus i := M.obj (Sum.inl i)
  minus i := M.obj (Sum.inr i)
  arrow e := M.map (Quiver.Hom.toPath e)

/-- A natural transformation restricts to a coordinate morphism. -/
def ofQuiverRepMap {M N : OpConjecture.Foundation.QuiverRep K (Vertex V)} (f : M ⟶ N) :
    ofQuiverRep M ⟶ ofQuiverRep N where
  plus i := f.app (Sum.inl i)
  minus i := f.app (Sum.inr i)
  comm := by
    intro i j e
    exact f.naturality
      (Quiver.Hom.toPath
        (show (Sum.inl i : Vertex V) ⟶ Sum.inr j from e))

/-- The restriction functor from separated-quiver representations to
coordinate data. -/
def ofQuiverRepFunctor :
    OpConjecture.Foundation.QuiverRep K (Vertex V) ⥤
      RepresentationData.{uK, uV, v, w} K V where
  obj := ofQuiverRep
  map := ofQuiverRepMap
  map_id M := by
    apply Hom.ext <;> funext i <;> rfl
  map_comp f g := by
    apply Hom.ext <;> funext i <;> rfl

instance toQuiverRepFunctor_faithful :
    (toQuiverRepFunctor (K := K) (V := V)).Faithful where
  map_injective := by
    intro D E f g h
    apply Hom.ext
    · funext i
      exact congrArg (fun q ↦ q.app (Sum.inl i)) h
    · funext i
      exact congrArg (fun q ↦ q.app (Sum.inr i)) h

instance toQuiverRepFunctor_full :
    (toQuiverRepFunctor (K := K) (V := V)).Full where
  map_surjective := by
    intro D E f
    let g : D ⟶ E :=
      { plus := fun i ↦ f.app (Sum.inl i)
        minus := fun i ↦ f.app (Sum.inr i)
        comm := by
          intro i j e
          have h := f.naturality
            (Quiver.Hom.toPath
              (show (Sum.inl i : Vertex V) ⟶ Sum.inr j from e))
          change D.toQuiverRep.map
                (Quiver.Hom.toPath
                  (show (Sum.inl i : Vertex V) ⟶ Sum.inr j from e)) ≫
                f.app (Sum.inr j) =
              f.app (Sum.inl i) ≫ E.toQuiverRep.map
                (Quiver.Hom.toPath
                  (show (Sum.inl i : Vertex V) ⟶ Sum.inr j from e)) at h
          rw [toQuiverRep_map_arrow, toQuiverRep_map_arrow] at h
          change D.arrow e ≫ f.app (Sum.inr j) =
            f.app (Sum.inl i) ≫ E.arrow e at h
          exact h }
    refine ⟨g, ?_⟩
    ext x
    cases x <;> rfl

/-- Reconstructing a representation from its vertex spaces and arrow maps
gives a naturally isomorphic representation. -/
def toOfQuiverRepIso (M : OpConjecture.Foundation.QuiverRep K (Vertex V)) :
    (toQuiverRepFunctor (K := K) (V := V)).obj
        ((ofQuiverRepFunctor (K := K) (V := V)).obj M) ≅ M :=
  CategoryTheory.Paths.liftNatIso
    (fun x ↦ match x with
      | Sum.inl i => Iso.refl (M.obj (Sum.inl i))
      | Sum.inr i => Iso.refl (M.obj (Sum.inr i)))
    (by
      intro a b e
      cases a with
      | inl i =>
          cases b with
          | inl j => exact PEmpty.elim e
          | inr j =>
              change (ofQuiverRep M).toQuiverRep.map
                    (Quiver.Hom.toPath e) ≫ 𝟙 _ =
                𝟙 _ ≫ M.map (Quiver.Hom.toPath e)
              rw [toQuiverRep_map_arrow]
              change M.map (Quiver.Hom.toPath e) ≫ 𝟙 _ =
                𝟙 _ ≫ M.map (Quiver.Hom.toPath e)
              simp
      | inr i =>
          cases b with
          | inl j => exact PEmpty.elim e
          | inr j => exact PEmpty.elim e)

instance toQuiverRepFunctor_essSurj :
    (toQuiverRepFunctor (K := K) (V := V)).EssSurj where
  mem_essImage M :=
    ⟨ofQuiverRep M, ⟨toOfQuiverRepIso M⟩⟩

instance toQuiverRepFunctor_isEquivalence :
    (toQuiverRepFunctor (K := K) (V := V)).IsEquivalence where

/-- Coordinate data are categorically equivalent to representations of the
literal separated quiver. -/
def quiverRepEquivalence :
    RepresentationData.{uK, uV, v, w} K V ≌
      OpConjecture.Foundation.QuiverRep K (Vertex V) :=
  (toQuiverRepFunctor (K := K) (V := V)).asEquivalence

end RepresentationData

end OpConjecture.SeparatedQuiver
