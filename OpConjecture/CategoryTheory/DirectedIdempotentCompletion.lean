import Mathlib.CategoryTheory.Idempotents.Basic
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Directed finite-block idempotent splitting

Triangular idempotents split from their diagonal blocks.  Consequently, an
object admitting a finite directed decomposition into idempotent-complete
blocks has all idempotents split.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace OpConjecture.CategoryTheory.DirectedIdempotent

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
variable {X Y : C}

/-- The upper-triangular endomorphism with blocks `a`, `b`, and `d`.

Morphisms in `Mat_` use the same row-source convention: `b : X ⟶ Y` is
the upper-right block. -/
def upper (a : X ⟶ X) (b : X ⟶ Y) (d : Y ⟶ Y) :
    (X ⊞ Y) ⟶ (X ⊞ Y) :=
  biprod.lift
    (biprod.fst ≫ a)
    (biprod.fst ≫ b + biprod.snd ≫ d)

@[reassoc (attr := simp)]
lemma inl_upper (a : X ⟶ X) (b : X ⟶ Y) (d : Y ⟶ Y) :
    biprod.inl ≫ upper a b d = biprod.lift a b := by
  ext <;> simp [upper]

@[reassoc (attr := simp)]
lemma inr_upper (a : X ⟶ X) (b : X ⟶ Y) (d : Y ⟶ Y) :
    biprod.inr ≫ upper a b d = d ≫ biprod.inr := by
  ext <;> simp [upper]

@[reassoc (attr := simp)]
lemma upper_fst (a : X ⟶ X) (b : X ⟶ Y) (d : Y ⟶ Y) :
    upper a b d ≫ biprod.fst = biprod.fst ≫ a := by
  simp [upper]

@[reassoc (attr := simp)]
lemma upper_snd (a : X ⟶ X) (b : X ⟶ Y) (d : Y ⟶ Y) :
    upper a b d ≫ biprod.snd = biprod.fst ≫ b + biprod.snd ≫ d := by
  simp [upper]

lemma upper_comp
    (a a' : X ⟶ X) (b b' : X ⟶ Y) (d d' : Y ⟶ Y) :
    upper a b d ≫ upper a' b' d' =
      upper (a ≫ a') (a ≫ b' + b ≫ d') (d ≫ d') := by
  ext <;> simp [upper, Category.assoc, Preadditive.comp_add, Preadditive.add_comp]

lemma upper_id :
    upper (𝟙 X) 0 (𝟙 Y) = 𝟙 (X ⊞ Y) := by
  ext <;> simp [upper]

/-- The diagonal sum of splittings splits the block-diagonal endomorphism. -/
lemma split_upper_zero
    {a : X ⟶ X} {d : Y ⟶ Y}
    (ha : ∃ (A : C) (i : A ⟶ X) (e : X ⟶ A),
      i ≫ e = 𝟙 A ∧ e ≫ i = a)
    (hd : ∃ (D : C) (i : D ⟶ Y) (e : Y ⟶ D),
      i ≫ e = 𝟙 D ∧ e ≫ i = d) :
    ∃ (Z : C) (i : Z ⟶ (X ⊞ Y)) (e : (X ⊞ Y) ⟶ Z),
      i ≫ e = 𝟙 Z ∧ e ≫ i = upper a 0 d := by
  obtain ⟨A, iA, eA, hiA, heA⟩ := ha
  obtain ⟨D, iD, eD, hiD, heD⟩ := hd
  refine ⟨A ⊞ D, biprod.map iA iD, biprod.map eA eD, ?_, ?_⟩
  · ext <;> simp [hiA, hiD]
  · ext <;> simp [upper, heA, heD]

/-- An upper-triangular idempotent splits once its diagonal idempotents split.

The proof is the unitriangular conjugation with off-diagonal parameter
`t = b d - a b`. -/
theorem split_upper
    {a : X ⟶ X} {b : X ⟶ Y} {d : Y ⟶ Y}
    (ha : a ≫ a = a)
    (hd : d ≫ d = d)
    (hab : a ≫ b + b ≫ d = b)
    (sa : ∃ (A : C) (i : A ⟶ X) (e : X ⟶ A),
      i ≫ e = 𝟙 A ∧ e ≫ i = a)
    (sd : ∃ (D : C) (i : D ⟶ Y) (e : Y ⟶ D),
      i ≫ e = 𝟙 D ∧ e ≫ i = d) :
    ∃ (Z : C) (i : Z ⟶ (X ⊞ Y)) (e : (X ⊞ Y) ⟶ Z),
      i ≫ e = 𝟙 Z ∧ e ≫ i = upper a b d := by
  let t : X ⟶ Y := b ≫ d - a ≫ b
  let u : (X ⊞ Y) ⟶ (X ⊞ Y) := upper (𝟙 X) t (𝟙 Y)
  let uInv : (X ⊞ Y) ⟶ (X ⊞ Y) := upper (𝟙 X) (-t) (𝟙 Y)
  have huInv_u : uInv ≫ u = 𝟙 (X ⊞ Y) := by
    rw [show uInv ≫ u = upper (𝟙 X) (-(t) + t) (𝟙 Y) by
      simp [uInv, u, upper_comp]]
    simp [upper_id]
  have hu_uInv : u ≫ uInv = 𝟙 (X ⊞ Y) := by
    rw [show u ≫ uInv = upper (𝟙 X) (t + -(t)) (𝟙 Y) by
      simp [uInv, u, upper_comp]]
    simp [upper_id]
  let φ : X ⊞ Y ≅ X ⊞ Y :=
    { hom := u
      inv := uInv
      hom_inv_id := hu_uInv
      inv_hom_id := huInv_u }
  have hat : a ≫ t + b - t ≫ d = 0 := by
    have habd : a ≫ b ≫ d = 0 := by
      have h := congrArg (fun f : X ⟶ Y ↦ f ≫ d) hab
      simp only [Preadditive.add_comp, Category.assoc, hd] at h
      exact add_eq_right.mp h
    dsimp [t]
    simp only [Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc]
    simp only [← Category.assoc, ha, hd, habd, zero_sub, sub_zero]
    have cancel_of_add_eq (r s z : X ⟶ Y) (h : r + s = z) :
        -r + z - s = 0 := by
      rw [← h]
      abel
    exact cancel_of_add_eq (a ≫ b) (b ≫ d) b hab
  have hconj : upper a b d ≫ φ.hom = φ.hom ≫ upper a 0 d := by
    dsimp [φ, u]
    rw [upper_comp, upper_comp]
    simp only [Category.comp_id, Category.id_comp, comp_zero, zero_add,
      sub_eq_zero.mp hat]
  exact
    (CategoryTheory.Idempotents.split_iff_of_iso φ
      (upper a b d) (upper a 0 d) hconj).mpr
      (split_upper_zero sa sd)

/-- Induction step for directed additive categories: an idempotent on a
biproduct splits if morphisms from the second block back to the first vanish
and the two diagonal idempotents split. -/
theorem split_idempotent_biprod_of_hom_zero
    (p : (X ⊞ Y) ⟶ (X ⊞ Y))
    (hp : p ≫ p = p)
    (hYX : ∀ f : Y ⟶ X, f = 0)
    (sX : (biprod.inl ≫ p ≫ biprod.fst) ≫
        (biprod.inl ≫ p ≫ biprod.fst) = biprod.inl ≫ p ≫ biprod.fst →
      ∃ (A : C) (i : A ⟶ X) (e : X ⟶ A),
        i ≫ e = 𝟙 A ∧ e ≫ i = biprod.inl ≫ p ≫ biprod.fst)
    (sY : (biprod.inr ≫ p ≫ biprod.snd) ≫
        (biprod.inr ≫ p ≫ biprod.snd) = biprod.inr ≫ p ≫ biprod.snd →
      ∃ (D : C) (i : D ⟶ Y) (e : Y ⟶ D),
        i ≫ e = 𝟙 D ∧ e ≫ i = biprod.inr ≫ p ≫ biprod.snd) :
    ∃ (Z : C) (i : Z ⟶ (X ⊞ Y)) (e : (X ⊞ Y) ⟶ Z),
      i ≫ e = 𝟙 Z ∧ e ≫ i = p := by
  let a : X ⟶ X := biprod.inl ≫ p ≫ biprod.fst
  let b : X ⟶ Y := biprod.inl ≫ p ≫ biprod.snd
  let d : Y ⟶ Y := biprod.inr ≫ p ≫ biprod.snd
  have htri : p = upper a b d := by
    ext
    · simp [a, upper, Category.assoc]
    · simp [b, upper, Category.assoc]
    · simpa [upper, Category.assoc] using
        hYX (biprod.inr ≫ p ≫ biprod.fst)
    · simp [d, upper, Category.assoc]
  have hp' : upper a b d ≫ upper a b d = upper a b d := by
    rw [← htri, hp]
  have ha : a ≫ a = a := by
    have h := congrArg
      (fun q : (X ⊞ Y) ⟶ (X ⊞ Y) ↦ biprod.inl ≫ q ≫ biprod.fst) hp'
    simpa [upper_comp, Category.assoc] using h
  have hd : d ≫ d = d := by
    have h := congrArg
      (fun q : (X ⊞ Y) ⟶ (X ⊞ Y) ↦ biprod.inr ≫ q ≫ biprod.snd) hp'
    simpa [upper_comp, Category.assoc] using h
  have hab : a ≫ b + b ≫ d = b := by
    have h := congrArg
      (fun q : (X ⊞ Y) ⟶ (X ⊞ Y) ↦ biprod.inl ≫ q ≫ biprod.snd) hp'
    simpa [upper_comp, Category.assoc] using h
  rw [htri]
  exact split_upper ha hd hab
    (by simpa [a] using sX (by simpa [a] using ha))
    (by simpa [d] using sY (by simpa [d] using hd))

section IteratedBiproduct

variable [HasZeroObject C]

open scoped ZeroObject

/-- A right-associated biproduct of a finite ordered list of blocks. -/
def iteratedBiprod : List C → C
  | [] => 0
  | X :: xs => X ⊞ iteratedBiprod xs

/-- Every idempotent on a fixed object splits. -/
def IdempotentsSplitAt (X : C) : Prop :=
  ∀ (p : X ⟶ X), p ≫ p = p →
    ∃ (Y : C) (i : Y ⟶ X) (e : X ⟶ Y),
      i ≫ e = 𝟙 Y ∧ e ≫ i = p

/-- Directedness of an ordered pair of blocks: there are no morphisms from
the later block back to the earlier block. -/
def NoBackward (X Y : C) : Prop :=
  ∀ f : Y ⟶ X, f = 0

/-- If every summand in a list has zero Hom to `X`, then their iterated
biproduct has zero Hom to `X`. -/
lemma iteratedBiprod_hom_eq_zero {X : C} {xs : List C}
    (h : ∀ Y ∈ xs, NoBackward X Y)
    (f : iteratedBiprod xs ⟶ X) : f = 0 := by
  induction xs with
  | nil =>
      exact (isZero_zero C).eq_of_src f 0
  | cons Y ys ih =>
      change (Y ⊞ iteratedBiprod ys) ⟶ X at f
      change f = (0 : (Y ⊞ iteratedBiprod ys) ⟶ X)
      apply biprod.hom_ext'
      · rw [comp_zero]
        exact h Y (by simp) (biprod.inl ≫ f)
      · have hrest : ∀ Z ∈ ys, NoBackward X Z := by
          intro Z hZ
          exact h Z (by simp [hZ])
        rw [comp_zero]
        exact ih hrest (biprod.inr ≫ f)

/-- A finite directed list of idempotent-complete blocks has an
idempotent-complete iterated biproduct. -/
theorem idempotentsSplitAt_iteratedBiprod (xs : List C)
    (hdir : xs.Pairwise NoBackward)
    (hsplit : ∀ X ∈ xs, IdempotentsSplitAt X) :
    IdempotentsSplitAt (iteratedBiprod xs) := by
  induction xs with
  | nil =>
      intro p hp
      refine ⟨0, 𝟙 _, 𝟙 _, Category.comp_id _, ?_⟩
      exact (isZero_zero C).eq_of_src _ _
  | cons X xs ih =>
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hdir
      have hX : IdempotentsSplitAt X := hsplit X (by simp)
      have hxs : IdempotentsSplitAt (iteratedBiprod xs) :=
        ih htail (fun Y hY ↦ hsplit Y (by simp [hY]))
      intro p hp
      apply split_idempotent_biprod_of_hom_zero p hp
      · intro f
        exact iteratedBiprod_hom_eq_zero hhead f
      · exact fun ha ↦ hX _ ha
      · exact fun hd ↦ hxs _ hd

/-- The exact abstract interface needed to prove idempotent completeness by a
finite directed block decomposition. -/
structure DirectedBlockDecomposition where
  /-- Ordered blocks for each object. -/
  blocks : C → List C
  /-- Every object is isomorphic to the iterated biproduct of its blocks. -/
  decompositionIso : ∀ X : C, X ≅ iteratedBiprod (blocks X)
  /-- Later blocks have no morphisms back to earlier blocks. -/
  directed : ∀ X : C, (blocks X).Pairwise NoBackward
  /-- Every individual block has all idempotents split in the ambient
  category. -/
  blockSplit : ∀ (X : C) (B : C), B ∈ blocks X → IdempotentsSplitAt B

/-- A finite directed decomposition into idempotent-complete blocks makes the
ambient category idempotent complete. -/
theorem isIdempotentComplete_of_directedBlockDecomposition
    (D : DirectedBlockDecomposition (C := C)) :
    IsIdempotentComplete C := by
  refine ⟨?_⟩
  intro X p hp
  let φ := D.decompositionIso X
  let p' : iteratedBiprod (D.blocks X) ⟶ iteratedBiprod (D.blocks X) :=
    φ.inv ≫ p ≫ φ.hom
  have hp' : p' ≫ p' = p' := by
    dsimp [p']
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    slice_lhs 2 3 => rw [hp]
  have hs : IdempotentsSplitAt (iteratedBiprod (D.blocks X)) :=
    idempotentsSplitAt_iteratedBiprod (D.blocks X) (D.directed X)
      (D.blockSplit X)
  have hconj : p ≫ φ.hom = φ.hom ≫ p' := by
    dsimp [p']
    simp only [Iso.hom_inv_id_assoc]
  exact (CategoryTheory.Idempotents.split_iff_of_iso φ p p' hconj).mpr
    (hs p' hp')

end IteratedBiproduct

end OpConjecture.CategoryTheory.DirectedIdempotent
