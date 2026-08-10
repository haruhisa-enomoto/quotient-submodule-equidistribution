import OpConjecture.RepresentationTheory.SimpleLevels

/-!
# Relabel an indecomposable skeleton by its nonsimple and simple parts

Every chosen indecomposable skeleton has a canonical partition into the
representatives which are not simple and those which are simple.  This file
turns that partition into a new skeleton whose label type is a literal sum.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace OpConjecture.IndecomposableSkeleton

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

universe u v w x

variable {R : Type u} [Ring R] [IsNoetherianRing R]
variable {ι : Type v} {κ : Type x}

/-- Reindex a complete duplicate-free indecomposable skeleton along an
arbitrary equivalence of label types. -/
noncomputable def relabel
    (sigma : IndecomposableSkeleton.{u, v, w} R ι)
    (e : κ ≃ ι) :
    IndecomposableSkeleton.{u, x, w} R κ where
  obj i := sigma.obj (e i)
  indecomposable i := sigma.indecomposable (e i)
  finiteLength i := sigma.finiteLength (e i)
  eq_of_iso := by
    intro i j hij
    apply e.injective
    exact sigma.eq_of_iso hij
  complete := by
    intro X hX
    obtain ⟨i, ⟨h⟩⟩ := sigma.complete X hX
    refine ⟨e.symm i, ⟨h ≪≫ eqToIso ?_⟩⟩
    simp
  decomposes := by
    intro X
    obtain ⟨n, a, ⟨h⟩⟩ := sigma.decomposes X
    refine ⟨n, fun t ↦ e.symm (a t),
      ⟨h ≪≫ biproduct.mapIso (fun t ↦ eqToIso ?_)⟩⟩
    simp

@[simp]
theorem relabel_obj
    (sigma : IndecomposableSkeleton.{u, v, w} R ι)
    (e : κ ≃ ι) (i : κ) :
    (sigma.relabel e).obj i = sigma.obj (e i) :=
  rfl

/-- The indices represented by nonsimple objects. -/
def NonsimpleIndex
    (sigma : IndecomposableSkeleton.{u, v, w} R ι) :=
  {i : ι // ¬ Simple (sigma.obj i)}

/-- The canonical equivalence from the literal nonsimple/simple partition
back to the original label type. -/
noncomputable def nonsimpleSimpleEquiv
    (sigma : IndecomposableSkeleton.{u, v, w} R ι) :
    NonsimpleIndex sigma ⊕ SimpleIndex sigma ≃ ι := by
  classical
  exact
    { toFun := Sum.elim Subtype.val Subtype.val
      invFun := fun i ↦ if h : Simple (sigma.obj i) then
          Sum.inr ⟨i, h⟩
        else
          Sum.inl ⟨i, h⟩
      left_inv := by
        intro i
        rcases i with i | i
        · simp [i.2]
        · simp [i.2]
      right_inv := by
        intro i
        by_cases h : Simple (sigma.obj i) <;> simp [h] }

@[simp]
theorem nonsimpleSimpleEquiv_inl
    (sigma : IndecomposableSkeleton.{u, v, w} R ι)
    (i : NonsimpleIndex sigma) :
    sigma.nonsimpleSimpleEquiv (Sum.inl i) = i.1 :=
  rfl

@[simp]
theorem nonsimpleSimpleEquiv_inr
    (sigma : IndecomposableSkeleton.{u, v, w} R ι)
    (i : SimpleIndex sigma) :
    sigma.nonsimpleSimpleEquiv (Sum.inr i) = i.1 :=
  rfl

/-- The skeleton with its nonsimple and simple representatives literally
separated into the two summands of its label type. -/
noncomputable def nonsimpleSimpleSkeleton
    (sigma : IndecomposableSkeleton.{u, v, w} R ι) :
    IndecomposableSkeleton.{u, v, w} R
      (NonsimpleIndex sigma ⊕ SimpleIndex sigma) :=
  sigma.relabel sigma.nonsimpleSimpleEquiv

@[simp]
theorem nonsimpleSimpleSkeleton_obj_inl
    (sigma : IndecomposableSkeleton.{u, v, w} R ι)
    (i : NonsimpleIndex sigma) :
    sigma.nonsimpleSimpleSkeleton.obj (Sum.inl i) = sigma.obj i.1 := by
  simp [nonsimpleSimpleSkeleton]

@[simp]
theorem nonsimpleSimpleSkeleton_obj_inr
    (sigma : IndecomposableSkeleton.{u, v, w} R ι)
    (i : SimpleIndex sigma) :
    sigma.nonsimpleSimpleSkeleton.obj (Sum.inr i) = sigma.obj i.1 := by
  simp [nonsimpleSimpleSkeleton]

end OpConjecture.IndecomposableSkeleton
