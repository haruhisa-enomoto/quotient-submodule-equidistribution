import Mathlib.Data.Finset.Sort
import OpConjecture.RepresentationDirected.ARWordCombinatorics
import OpConjecture.RepresentationDirected.DirectedARTwoOrbits

/-!
# The ordered Auslander--Reiten word

This file gives the paper-facing dictionary between the selected directed
linear order on a finite indecomposable skeleton and the finite word of
projective translation-orbit labels.  It contains no concrete algebra or
module classification.
-/

noncomputable section

open CategoryTheory

namespace OpConjecture.RepresentationDirected.DirectedAROrbit.OrderedARWord

open TwoOrbits

universe uR uIota

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {Iota : Type uIota} [Fintype Iota]
  (sigma : IndecomposableSkeleton.{uR, uIota, uR} R Iota)

abbrev ARData := sigma.FiniteARTranslationData

/-- Increasing enumeration for a specified directed linear order. -/
def orderedObjectEquivFor
    (E : DirectedOrderChoice sigma) :
    Fin (Fintype.card Iota) ≃ Iota := by
  letI := E.order
  exact (Fintype.orderIsoFinOfCardEq Iota rfl).toEquiv

/-- The object at a specified position for an explicit directed order. -/
def orderedObjectFor
    (E : DirectedOrderChoice sigma)
    (k : Fin (Fintype.card Iota)) : Iota :=
  orderedObjectEquivFor sigma E k

/-- The AR word attached to a specified directed linear order. -/
def wordFor
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (E : DirectedOrderChoice sigma) :
    List (ProjectiveLabel sigma) :=
  List.ofFn fun k : Fin (Fintype.card Iota) ↦
    arOrbitLabel sigma H D (orderedObjectFor sigma E k)

@[simp] theorem wordFor_length
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (E : DirectedOrderChoice sigma) :
    (wordFor sigma H D E).length = Fintype.card Iota := by
  simp [wordFor]

/-- Positions of an explicit-order AR word, identified with the
indecomposable labels. -/
def positionEquivFor
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (E : DirectedOrderChoice sigma) :
    Fin (wordFor sigma H D E).length ≃ Iota :=
  (finCongr (wordFor_length sigma H D E)).trans
    (orderedObjectEquivFor sigma E)

@[simp] theorem positionEquivFor_symm_apply_apply
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (E : DirectedOrderChoice sigma) (x : Iota) :
    positionEquivFor sigma H D E
        ((positionEquivFor sigma H D E).symm x) = x :=
  (positionEquivFor sigma H D E).apply_symm_apply x

@[simp] theorem positionEquivFor_apply_symm_apply
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (E : DirectedOrderChoice sigma)
    (p : Fin (wordFor sigma H D E).length) :
    (positionEquivFor sigma H D E).symm
        (positionEquivFor sigma H D E p) = p :=
  (positionEquivFor sigma H D E).symm_apply_apply p

/-- The explicit position equivalence is increasing for its specified
directed order. -/
theorem positionFor_lt_iff
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (E : DirectedOrderChoice sigma)
    (p q : Fin (wordFor sigma H D E).length) :
    letI := E.order
    positionEquivFor sigma H D E p < positionEquivFor sigma H D E q ↔
      p < q := by
  letI := E.order
  change (Fintype.orderIsoFinOfCardEq Iota rfl)
      (finCongr (wordFor_length sigma H D E) p) <
    (Fintype.orderIsoFinOfCardEq Iota rfl)
      (finCongr (wordFor_length sigma H D E) q) ↔ p < q
  rw [(Fintype.orderIsoFinOfCardEq Iota rfl).lt_iff_lt]
  rfl

/-- Reading an explicit-order word at a position gives the orbit label of
the corresponding indecomposable. -/
@[simp] theorem label_wordFor
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (E : DirectedOrderChoice sigma)
    (p : Fin (wordFor sigma H D E).length) :
    ARWord.label (wordFor sigma H D E) p =
      arOrbitLabel sigma H D (positionEquivFor sigma H D E p) := by
  letI := E.order
  rw [show ARWord.label (wordFor sigma H D E) p =
      (wordFor sigma H D E).get p from rfl]
  simp only [wordFor, List.get_ofFn, orderedObjectFor,
    orderedObjectEquivFor, positionEquivFor]
  apply congrArg (arOrbitLabel sigma H D)
  rfl

/-- `ARWord.IsPrevious` in an explicit-order word is exactly immediate
predecessorship in the corresponding translation orbit for that order. -/
theorem isPrevious_wordFor_iff_isPreviousInOrbitFor
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (E : DirectedOrderChoice sigma)
    (p x : Fin (wordFor sigma H D E).length) :
    ARWord.IsPrevious (wordFor sigma H D E) p x ↔
      letI := E.order
      IsPreviousInOrbitFor sigma H D
        (positionEquivFor sigma H D E p)
        (positionEquivFor sigma H D E x) := by
  letI := E.order
  constructor
  · rintro ⟨hpx, hlabel, hnone⟩
    refine ⟨(positionFor_lt_iff sigma H D E p x).2 hpx, ?_, ?_⟩
    · simpa only [label_wordFor] using hlabel
    · intro z hpz hzx hzlabel
      let q : Fin (wordFor sigma H D E).length :=
        (positionEquivFor sigma H D E).symm z
      have hpq : p < q := by
        apply (positionFor_lt_iff sigma H D E p q).1
        simpa only [q, positionEquivFor_symm_apply_apply] using hpz
      have hqx : q < x := by
        apply (positionFor_lt_iff sigma H D E q x).1
        simpa only [q, positionEquivFor_symm_apply_apply] using hzx
      apply hnone q hpq hqx
      simpa only [label_wordFor, q,
        positionEquivFor_symm_apply_apply] using hzlabel
  · rintro ⟨hpx, hlabel, hnone⟩
    refine ⟨(positionFor_lt_iff sigma H D E p x).1 hpx, ?_, ?_⟩
    · simpa only [label_wordFor] using hlabel
    · intro q hpq hqx hqLabel
      apply hnone (positionEquivFor sigma H D E q)
      · exact (positionFor_lt_iff sigma H D E p q).2 hpq
      · exact (positionFor_lt_iff sigma H D E q x).2 hqx
      · simpa only [label_wordFor] using hqLabel

/-- A position in an explicit-order AR word has a preceding occurrence
precisely when its indecomposable is nonprojective. -/
theorem exists_previous_positionFor_iff_not_projective
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (E : DirectedOrderChoice sigma) (x : Iota) :
    (∃ p : Fin (wordFor sigma H D E).length,
      ARWord.IsPrevious (wordFor sigma H D E) p
        ((positionEquivFor sigma H D E).symm x)) ↔
      ¬ Projective (sigma.obj x) := by
  letI := E.order
  let HO : DirectedHomOrder sigma := E.directedHomOrder sigma
  constructor
  · rintro ⟨p, hp⟩
    apply (exists_isPreviousInOrbitFor_iff_not_projective
      sigma H HO D x).1
    refine ⟨positionEquivFor sigma H D E p, ?_⟩
    simpa only [positionEquivFor_symm_apply_apply] using
      (isPrevious_wordFor_iff_isPreviousInOrbitFor
        sigma H D E p ((positionEquivFor sigma H D E).symm x)).1 hp
  · intro hx
    obtain ⟨p, hp⟩ :=
      (exists_isPreviousInOrbitFor_iff_not_projective
        sigma H HO D x).2 hx
    refine ⟨(positionEquivFor sigma H D E).symm p, ?_⟩
    apply (isPrevious_wordFor_iff_isPreviousInOrbitFor
      sigma H D E _ _).2
    simpa only [positionEquivFor_symm_apply_apply] using hp

/-- At a nonprojective vertex, the previous occurrence in an explicit-order
word is literally the position occupied by its AR translate. -/
theorem isPrevious_positionFor_iff_eq_arTranslation
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (E : DirectedOrderChoice sigma)
    (x : sigma.NonprojectiveLabel)
    (p : Fin (wordFor sigma H D E).length) :
    ARWord.IsPrevious (wordFor sigma H D E) p
        ((positionEquivFor sigma H D E).symm x.1) ↔
      positionEquivFor sigma H D E p = (D.arTranslation sigma x).1 := by
  letI := E.order
  let HO : DirectedHomOrder sigma := E.directedHomOrder sigma
  rw [isPrevious_wordFor_iff_isPreviousInOrbitFor]
  simpa only [positionEquivFor_symm_apply_apply] using
    (isPreviousInOrbitFor_iff_eq_arTranslation sigma H HO D x
      (positionEquivFor sigma H D E p))

/-- Increasing enumeration of the selected directed linear order, regarded
first as an equivalence so its type does not export a local order instance. -/
def orderedObjectEquiv
    (H : HasAcyclicNonzeroNonisomorphisms sigma) :
    Fin (Fintype.card Iota) ≃ Iota := by
  letI := directedLinearOrder sigma H
  exact (Fintype.orderIsoFinOfCardEq Iota rfl).toEquiv

def orderedObject
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (k : Fin (Fintype.card Iota)) : Iota :=
  orderedObjectEquiv sigma H k

/-- The actual finite AR word: enumerate all indecomposables in the selected
directed order and retain their projective translation-orbit labels. -/
def word
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) : List (ProjectiveLabel sigma) :=
  List.ofFn fun k : Fin (Fintype.card Iota) ↦
    arOrbitLabel sigma H D (orderedObject sigma H k)

/-- The existing word is the explicit-order word for the default chosen
linear extension. -/
theorem wordFor_chosen
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) :
    wordFor sigma H D (.chosen sigma H) = word sigma H D := by
  rfl

@[simp] theorem word_length
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) :
    (word sigma H D).length = Fintype.card Iota := by
  simp [word]

/-- Positions of the actual word, identified with indecomposable labels. -/
def positionEquiv
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) : Fin (word sigma H D).length ≃ Iota :=
  (finCongr (word_length sigma H D)).trans (orderedObjectEquiv sigma H)

/-- The explicit position equivalence specializes definitionally to the
default chosen-order equivalence. -/
theorem positionEquivFor_chosen_eq
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) :
    positionEquivFor sigma H D (.chosen sigma H) =
      positionEquiv sigma H D := by
  rfl

@[simp] theorem positionEquiv_symm_apply_apply
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (x : Iota) :
    positionEquiv sigma H D
        ((positionEquiv sigma H D).symm x) = x :=
  (positionEquiv sigma H D).apply_symm_apply x

@[simp] theorem positionEquiv_apply_symm_apply
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (p : Fin (word sigma H D).length) :
    (positionEquiv sigma H D).symm
        (positionEquiv sigma H D p) = p :=
  (positionEquiv sigma H D).symm_apply_apply p

/-- The position equivalence is increasing for the selected directed order. -/
theorem position_lt_iff
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (p q : Fin (word sigma H D).length) :
    letI := directedLinearOrder sigma H
    positionEquiv sigma H D p < positionEquiv sigma H D q ↔ p < q := by
  letI := directedLinearOrder sigma H
  change (Fintype.orderIsoFinOfCardEq Iota rfl)
      (finCongr (word_length sigma H D) p) <
    (Fintype.orderIsoFinOfCardEq Iota rfl)
      (finCongr (word_length sigma H D) q) ↔ p < q
  rw [(Fintype.orderIsoFinOfCardEq Iota rfl).lt_iff_lt]
  rfl

/-- Reading the word at a position gives the orbit label of the corresponding
indecomposable. -/
@[simp] theorem label_word
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (p : Fin (word sigma H D).length) :
    ARWord.label (word sigma H D) p =
      arOrbitLabel sigma H D (positionEquiv sigma H D p) := by
  letI := directedLinearOrder sigma H
  rw [show ARWord.label (word sigma H D) p =
      (word sigma H D).get p from rfl]
  simp only [word, List.get_ofFn, orderedObject, orderedObjectEquiv,
    positionEquiv]
  apply congrArg (arOrbitLabel sigma H D)
  rfl

/-- `ARWord.IsPrevious` in the concrete ordered word is exactly the intrinsic
immediate-predecessor relation in a translation orbit. -/
theorem isPrevious_word_iff_isPreviousInOrbit
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (p x : Fin (word sigma H D).length) :
    ARWord.IsPrevious (word sigma H D) p x ↔
      IsPreviousInOrbit sigma H D
        (positionEquiv sigma H D p) (positionEquiv sigma H D x) := by
  letI := directedLinearOrder sigma H
  constructor
  · rintro ⟨hpx, hlabel, hnone⟩
    refine ⟨(position_lt_iff sigma H D p x).2 hpx, ?_, ?_⟩
    · simpa only [label_word] using hlabel
    · intro z hpz hzx hzlabel
      let q : Fin (word sigma H D).length :=
        (positionEquiv sigma H D).symm z
      have hpq : p < q := by
        apply (position_lt_iff sigma H D p q).1
        simpa only [q, positionEquiv_symm_apply_apply] using hpz
      have hqx : q < x := by
        apply (position_lt_iff sigma H D q x).1
        simpa only [q, positionEquiv_symm_apply_apply] using hzx
      apply hnone q hpq hqx
      simpa only [label_word, q, positionEquiv_symm_apply_apply] using hzlabel
  · rintro ⟨hpx, hlabel, hnone⟩
    refine ⟨(position_lt_iff sigma H D p x).1 hpx, ?_, ?_⟩
    · simpa only [label_word] using hlabel
    · intro q hpq hqx hqLabel
      apply hnone (positionEquiv sigma H D q)
      · exact (position_lt_iff sigma H D p q).2 hpq
      · exact (position_lt_iff sigma H D q x).2 hqx
      · simpa only [label_word] using hqLabel

/-- A position in the ordered AR word has a previous occurrence precisely
when its indecomposable is nonprojective. -/
theorem exists_previous_position_iff_not_projective
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (x : Iota) :
    (∃ p : Fin (word sigma H D).length,
      ARWord.IsPrevious (word sigma H D) p
        ((positionEquiv sigma H D).symm x)) ↔
      ¬ Projective (sigma.obj x) := by
  constructor
  · rintro ⟨p, hp⟩
    apply (exists_isPreviousInOrbit_iff_not_projective sigma H D x).1
    refine ⟨positionEquiv sigma H D p, ?_⟩
    simpa only [positionEquiv_symm_apply_apply] using
      (isPrevious_word_iff_isPreviousInOrbit sigma H D p
        ((positionEquiv sigma H D).symm x)).1 hp
  · intro hx
    obtain ⟨p, hp⟩ :=
      (exists_isPreviousInOrbit_iff_not_projective sigma H D x).2 hx
    refine ⟨(positionEquiv sigma H D).symm p, ?_⟩
    apply (isPrevious_word_iff_isPreviousInOrbit sigma H D _ _).2
    simpa only [positionEquiv_symm_apply_apply] using hp

/-- At a nonprojective vertex, the previous occurrence in the actual word is
literally the position occupied by its AR translate. -/
theorem isPrevious_position_iff_eq_arTranslation
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (x : sigma.NonprojectiveLabel)
    (p : Fin (word sigma H D).length) :
    ARWord.IsPrevious (word sigma H D) p
        ((positionEquiv sigma H D).symm x.1) ↔
      positionEquiv sigma H D p = (D.arTranslation sigma x).1 := by
  rw [isPrevious_word_iff_isPreviousInOrbit]
  simpa only [positionEquiv_symm_apply_apply] using
    (isPreviousInOrbit_iff_eq_arTranslation sigma H D x
      (positionEquiv sigma H D p))

/-- There is an oriented irreducible arrow from orbit `a` to orbit `b`. -/
def HasOrientedOrbitArrow
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (a b : ProjectiveLabel sigma) : Prop :=
  ∃ u v : Iota,
    HasIrreducibleMorphism (sigma.obj u) (sigma.obj v) ∧
      arOrbitLabel sigma H D u = a ∧
      arOrbitLabel sigma H D v = b

/-- The simple graph underlying the orbit graph of the directed AR quiver. -/
def orbitGraph
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) : SimpleGraph (ProjectiveLabel sigma) where
  Adj a b := HasOrientedOrbitArrow sigma H D a b ∨
    HasOrientedOrbitArrow sigma H D b a
  symm := by
    constructor
    intro a b hab
    exact hab.elim Or.inr Or.inl
  loopless := by
    constructor
    intro a haa
    rcases haa with haa | haa
    · obtain ⟨u, v, huv, hu, hv⟩ := haa
      exact seed_arOrbitLabel_ne sigma H D huv (hu.trans hv.symm)
    · obtain ⟨u, v, huv, hu, hv⟩ := haa
      exact seed_arOrbitLabel_ne sigma H D huv (hu.trans hv.symm)

/-- Consecutive occurrences of one orbit label differ by exactly one in AR
height. -/
theorem arHeight_eq_add_one_of_isPreviousInOrbit
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) {p x : Iota}
    (hpx : IsPreviousInOrbit sigma H D p x) :
    arHeight sigma D x = arHeight sigma D p + 1 := by
  have hxNonprojective : ¬ Projective (sigma.obj x) :=
    (exists_isPreviousInOrbit_iff_not_projective sigma H D x).1 ⟨p, hpx⟩
  let xn : sigma.NonprojectiveLabel := ⟨x, hxNonprojective⟩
  have hp : p = (D.arTranslation sigma xn).1 :=
    (isPreviousInOrbit_iff_eq_arTranslation sigma H D xn p).1 hpx
  have hheight := arHeight_translation sigma H D xn
  simpa only [xn, ← hp] using hheight

/-- Every adjacent pair of translation-orbit labels has the manuscript's
interior alternation property in the actual ordered AR word.  The proof uses
the exact weak/strict cross-height inequalities of the two-orbit theorem: the
open interval between consecutive heights on one orbit can contain at most
one height on an adjacent orbit. -/
theorem word_hasInteriorAlternation
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) :
    ARWord.HasInteriorAlternation (orbitGraph sigma H D) (word sigma H D) := by
  intro p x y z hpx hadj hpy hyx hpz hzx hzLabel
  letI := directedLinearOrder sigma H
  have hpxObj : IsPreviousInOrbit sigma H D
      (positionEquiv sigma H D p) (positionEquiv sigma H D x) :=
    (isPrevious_word_iff_isPreviousInOrbit sigma H D p x).1 hpx
  have hpyObj : positionEquiv sigma H D p < positionEquiv sigma H D y :=
    (position_lt_iff sigma H D p y).2 hpy
  have hyxObj : positionEquiv sigma H D y < positionEquiv sigma H D x :=
    (position_lt_iff sigma H D y x).2 hyx
  have hpzObj : positionEquiv sigma H D p < positionEquiv sigma H D z :=
    (position_lt_iff sigma H D p z).2 hpz
  have hzxObj : positionEquiv sigma H D z < positionEquiv sigma H D x :=
    (position_lt_iff sigma H D z x).2 hzx
  have hxHeight : arHeight sigma D (positionEquiv sigma H D x) =
      arHeight sigma D (positionEquiv sigma H D p) + 1 :=
    arHeight_eq_add_one_of_isPreviousInOrbit sigma H D hpxObj
  have hzOrbit :
      arOrbitLabel sigma H D (positionEquiv sigma H D z) =
        arOrbitLabel sigma H D (positionEquiv sigma H D y) := by
    simpa only [label_word] using hzLabel
  have hadjObj :
      HasOrientedOrbitArrow sigma H D
          (arOrbitLabel sigma H D (positionEquiv sigma H D p))
          (arOrbitLabel sigma H D (positionEquiv sigma H D y)) ∨
        HasOrientedOrbitArrow sigma H D
          (arOrbitLabel sigma H D (positionEquiv sigma H D y))
          (arOrbitLabel sigma H D (positionEquiv sigma H D p)) := by
    simpa only [orbitGraph, label_word] using hadj
  rcases hadjObj with hforward | hreverse
  · obtain ⟨u, v, huv, hu, hv⟩ := hforward
    have hpOrbitU :
        arOrbitLabel sigma H D (positionEquiv sigma H D p) =
          arOrbitLabel sigma H D u := hu.symm
    have hyOrbitV :
        arOrbitLabel sigma H D (positionEquiv sigma H D y) =
          arOrbitLabel sigma H D v := hv.symm
    have hxOrbitU :
        arOrbitLabel sigma H D (positionEquiv sigma H D x) =
          arOrbitLabel sigma H D u := hpxObj.2.1.symm.trans hu.symm
    have hzOrbitV :
        arOrbitLabel sigma H D (positionEquiv sigma H D z) =
          arOrbitLabel sigma H D v := hzOrbit.trans hv.symm
    have hyLower :=
      (lt_iff_seed_cross_height_le sigma H D huv hpOrbitU hyOrbitV).1
        hpyObj
    have hyUpper :=
      (reverse_lt_iff_seed_cross_height_gt sigma H D huv hxOrbitU hyOrbitV).1
        hyxObj
    have hzLower :=
      (lt_iff_seed_cross_height_le sigma H D huv hpOrbitU hzOrbitV).1
        hpzObj
    have hzUpper :=
      (reverse_lt_iff_seed_cross_height_gt sigma H D huv hxOrbitU hzOrbitV).1
        hzxObj
    apply (positionEquiv sigma H D).injective
    apply eq_of_arOrbitLabel_eq_of_arHeight_eq sigma H D hzOrbit
    omega
  · obtain ⟨u, v, huv, hu, hv⟩ := hreverse
    have hyOrbitU :
        arOrbitLabel sigma H D (positionEquiv sigma H D y) =
          arOrbitLabel sigma H D u := hu.symm
    have hpOrbitV :
        arOrbitLabel sigma H D (positionEquiv sigma H D p) =
          arOrbitLabel sigma H D v := hv.symm
    have hzOrbitU :
        arOrbitLabel sigma H D (positionEquiv sigma H D z) =
          arOrbitLabel sigma H D u := hzOrbit.trans hu.symm
    have hxOrbitV :
        arOrbitLabel sigma H D (positionEquiv sigma H D x) =
          arOrbitLabel sigma H D v := hpxObj.2.1.symm.trans hv.symm
    have hyLower :=
      (reverse_lt_iff_seed_cross_height_gt sigma H D huv hyOrbitU hpOrbitV).1
        hpyObj
    have hyUpper :=
      (lt_iff_seed_cross_height_le sigma H D huv hyOrbitU hxOrbitV).1
        hyxObj
    have hzLower :=
      (reverse_lt_iff_seed_cross_height_gt sigma H D huv hzOrbitU hpOrbitV).1
        hpzObj
    have hzUpper :=
      (lt_iff_seed_cross_height_le sigma H D huv hzOrbitU hxOrbitV).1
        hzxObj
    apply (positionEquiv sigma H D).injective
    apply eq_of_arOrbitLabel_eq_of_arHeight_eq sigma H D hzOrbit
    omega

/-- Inside one translation orbit, the directed order is exactly the height
order. -/
theorem lt_iff_arHeight_lt_of_arOrbitLabel_eq
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) {x y : Iota}
    (horbit : arOrbitLabel sigma H D x = arOrbitLabel sigma H D y) :
    letI := directedLinearOrder sigma H
    x < y ↔ arHeight sigma D x < arHeight sigma D y := by
  letI := directedLinearOrder sigma H
  constructor
  · intro hxy
    rcases arReach_or_arReach_of_arOrbitLabel_eq sigma H D horbit with
      hreach | hback
    · exact arHeight_lt_of_arReach_of_ne sigma H D hreach hxy.ne
    · exact False.elim ((not_le_of_gt hxy) (arReach_le sigma H D hback))
  · intro hheight
    have hreach := arReach_of_arOrbitLabel_eq_of_arHeight_le
      sigma H D horbit hheight.le
    exact lt_of_le_of_ne (arReach_le sigma H D hreach)
      (fun hxy ↦ by subst y; omega)

/-- Literal boundary-run form of the two-orbit interlacing theorem for the
actual ordered AR word.  In every adjacent two-label projection, only its
first and last runs may contain repeated letters. -/
theorem word_hasOnlyBoundaryRepeatedRuns
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) :
    ARWord.HasOnlyBoundaryRepeatedRuns
      (orbitGraph sigma H D) (word sigma H D) := by
  rw [ARWord.hasOnlyBoundaryRepeatedRuns_iff]
  intro a b hab x y hxy hxa hya hbetween
  by_contra hboundary
  push Not at hboundary
  obtain ⟨z, hzx, hzb⟩ := hboundary.1
  obtain ⟨w, hyw, hwb⟩ := hboundary.2
  letI := directedLinearOrder sigma H
  have hzxObj : positionEquiv sigma H D z < positionEquiv sigma H D x :=
    (position_lt_iff sigma H D z x).2 hzx
  have hxyObj : positionEquiv sigma H D x < positionEquiv sigma H D y :=
    (position_lt_iff sigma H D x y).2 hxy
  have hywObj : positionEquiv sigma H D y < positionEquiv sigma H D w :=
    (position_lt_iff sigma H D y w).2 hyw
  have hxyOrbit :
      arOrbitLabel sigma H D (positionEquiv sigma H D x) =
        arOrbitLabel sigma H D (positionEquiv sigma H D y) := by
    simpa only [label_word] using hxa.trans hya.symm
  have hxHeightLt :
      arHeight sigma D (positionEquiv sigma H D x) <
        arHeight sigma D (positionEquiv sigma H D y) :=
    (lt_iff_arHeight_lt_of_arOrbitLabel_eq sigma H D hxyOrbit).1 hxyObj
  have hzOrbitB :
      arOrbitLabel sigma H D (positionEquiv sigma H D z) = b := by
    simpa only [label_word] using hzb
  have hwOrbitB :
      arOrbitLabel sigma H D (positionEquiv sigma H D w) = b := by
    simpa only [label_word] using hwb
  have hxOrbitA :
      arOrbitLabel sigma H D (positionEquiv sigma H D x) = a := by
    simpa only [label_word] using hxa
  have hyOrbitA :
      arOrbitLabel sigma H D (positionEquiv sigma H D y) = a := by
    simpa only [label_word] using hya
  have habObj :
      HasOrientedOrbitArrow sigma H D a b ∨
        HasOrientedOrbitArrow sigma H D b a := by
    simpa only [orbitGraph] using hab
  rcases habObj with habForward | habReverse
  · obtain ⟨u, v, huv, hu, hv⟩ := habForward
    have hxOrbitU :
        arOrbitLabel sigma H D (positionEquiv sigma H D x) =
          arOrbitLabel sigma H D u := hxOrbitA.trans hu.symm
    have hyOrbitU :
        arOrbitLabel sigma H D (positionEquiv sigma H D y) =
          arOrbitLabel sigma H D u := hyOrbitA.trans hu.symm
    have hzOrbitV :
        arOrbitLabel sigma H D (positionEquiv sigma H D z) =
          arOrbitLabel sigma H D v := hzOrbitB.trans hv.symm
    have hwOrbitV :
        arOrbitLabel sigma H D (positionEquiv sigma H D w) =
          arOrbitLabel sigma H D v := hwOrbitB.trans hv.symm
    have hzBefore :=
      (reverse_lt_iff_seed_cross_height_gt sigma H D huv hxOrbitU hzOrbitV).1
        hzxObj
    have hyBeforeW :=
      (lt_iff_seed_cross_height_le sigma H D huv hyOrbitU hwOrbitV).1
        hywObj
    let n : ℕ :=
      arHeight sigma D (positionEquiv sigma H D x) + arHeight sigma D v -
        arHeight sigma D u
    have huLe : arHeight sigma D u ≤
        arHeight sigma D (positionEquiv sigma H D x) + arHeight sigma D v := by
      omega
    have hnEq : n + arHeight sigma D u =
        arHeight sigma D (positionEquiv sigma H D x) + arHeight sigma D v := by
      exact Nat.sub_add_cancel huLe
    have hnLeW : n ≤ arHeight sigma D (positionEquiv sigma H D w) := by
      omega
    obtain ⟨tObj, htOrbitW, htHeight⟩ :=
      exists_arOrbitLabel_eq_arHeight_eq_of_le sigma H D
        (positionEquiv sigma H D w) n hnLeW
    let t : Fin (word sigma H D).length :=
      (positionEquiv sigma H D).symm tObj
    have htObj : positionEquiv sigma H D t = tObj := by
      simp only [t, positionEquiv_symm_apply_apply]
    have htOrbitV : arOrbitLabel sigma H D tObj =
        arOrbitLabel sigma H D v := htOrbitW.trans hwOrbitV
    have hxtObj : positionEquiv sigma H D x < tObj := by
      apply (lt_iff_seed_cross_height_le sigma H D huv hxOrbitU htOrbitV).2
      rw [htHeight, hnEq]
    have htyObj : tObj < positionEquiv sigma H D y := by
      apply (reverse_lt_iff_seed_cross_height_gt sigma H D huv
        hyOrbitU htOrbitV).2
      rw [htHeight, hnEq]
      omega
    have hxt : x < t := by
      apply (position_lt_iff sigma H D x t).1
      simpa only [htObj] using hxtObj
    have hty : t < y := by
      apply (position_lt_iff sigma H D t y).1
      simpa only [htObj] using htyObj
    apply hbetween t hxt hty
    rw [label_word, htObj, htOrbitV, hv]
  · obtain ⟨u, v, huv, hu, hv⟩ := habReverse
    have hzOrbitU :
        arOrbitLabel sigma H D (positionEquiv sigma H D z) =
          arOrbitLabel sigma H D u := hzOrbitB.trans hu.symm
    have hwOrbitU :
        arOrbitLabel sigma H D (positionEquiv sigma H D w) =
          arOrbitLabel sigma H D u := hwOrbitB.trans hu.symm
    have hxOrbitV :
        arOrbitLabel sigma H D (positionEquiv sigma H D x) =
          arOrbitLabel sigma H D v := hxOrbitA.trans hv.symm
    have hyOrbitV :
        arOrbitLabel sigma H D (positionEquiv sigma H D y) =
          arOrbitLabel sigma H D v := hyOrbitA.trans hv.symm
    have hzBefore :=
      (lt_iff_seed_cross_height_le sigma H D huv hzOrbitU hxOrbitV).1 hzxObj
    have hyBeforeW :=
      (reverse_lt_iff_seed_cross_height_gt sigma H D huv
        hwOrbitU hyOrbitV).1 hywObj
    let n : ℕ :=
      arHeight sigma D (positionEquiv sigma H D x) + arHeight sigma D u + 1 -
        arHeight sigma D v
    have hvLe : arHeight sigma D v ≤
        arHeight sigma D (positionEquiv sigma H D x) +
          arHeight sigma D u + 1 := by
      omega
    have hnEq : n + arHeight sigma D v =
        arHeight sigma D (positionEquiv sigma H D x) +
          arHeight sigma D u + 1 := by
      exact Nat.sub_add_cancel hvLe
    have hnLeW : n ≤ arHeight sigma D (positionEquiv sigma H D w) := by
      omega
    obtain ⟨tObj, htOrbitW, htHeight⟩ :=
      exists_arOrbitLabel_eq_arHeight_eq_of_le sigma H D
        (positionEquiv sigma H D w) n hnLeW
    let t : Fin (word sigma H D).length :=
      (positionEquiv sigma H D).symm tObj
    have htObj : positionEquiv sigma H D t = tObj := by
      simp only [t, positionEquiv_symm_apply_apply]
    have htOrbitU : arOrbitLabel sigma H D tObj =
        arOrbitLabel sigma H D u := htOrbitW.trans hwOrbitU
    have hxtObj : positionEquiv sigma H D x < tObj := by
      apply (reverse_lt_iff_seed_cross_height_gt sigma H D huv
        htOrbitU hxOrbitV).2
      rw [htHeight, hnEq]
      omega
    have htyObj : tObj < positionEquiv sigma H D y := by
      apply (lt_iff_seed_cross_height_le sigma H D huv htOrbitU hyOrbitV).2
      rw [htHeight, hnEq]
      omega
    have hxt : x < t := by
      apply (position_lt_iff sigma H D x t).1
      simpa only [htObj] using hxtObj
    have hty : t < y := by
      apply (position_lt_iff sigma H D t y).1
      simpa only [htObj] using htyObj
    apply hbetween t hxt hty
    rw [label_word, htObj, htOrbitU, hu]

/-- Every actual irreducible arrow is selected by the middle-position rule
in the ordered AR word. -/
theorem isMiddle_of_hasIrreducibleMorphism
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma)
    (y x : Fin (word sigma H D).length)
    (hyx : HasIrreducibleMorphism
      (sigma.obj (positionEquiv sigma H D y))
      (sigma.obj (positionEquiv sigma H D x))) :
    ARWord.IsMiddle (orbitGraph sigma H D) (word sigma H D) y x := by
  letI := directedLinearOrder sigma H
  let HO : DirectedHomOrder sigma :=
    DirectedHomOrder.of_acyclicNonzeroNonisomorphisms sigma H
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [orbitGraph, label_word] using
      (Or.inl ⟨positionEquiv sigma H D y,
        positionEquiv sigma H D x, hyx, rfl, rfl⟩ :
        HasOrientedOrbitArrow sigma H D
            (arOrbitLabel sigma H D (positionEquiv sigma H D y))
            (arOrbitLabel sigma H D (positionEquiv sigma H D x)) ∨
          HasOrientedOrbitArrow sigma H D
            (arOrbitLabel sigma H D (positionEquiv sigma H D x))
            (arOrbitLabel sigma H D (positionEquiv sigma H D y)))
  · exact (position_lt_iff sigma H D y x).1 (HO.lt_of_irreducible hyx)
  · intro p hpx
    have hpxObj :=
      (isPrevious_word_iff_isPreviousInOrbit sigma H D p x).1 hpx
    have hxNonprojective :
        ¬ Projective (sigma.obj (positionEquiv sigma H D x)) :=
      (exists_isPreviousInOrbit_iff_not_projective sigma H D
        (positionEquiv sigma H D x)).1
        ⟨positionEquiv sigma H D p, hpxObj⟩
    let xn : sigma.NonprojectiveLabel :=
      ⟨positionEquiv sigma H D x, hxNonprojective⟩
    have hpEq : positionEquiv sigma H D p =
        (D.arTranslation sigma xn).1 :=
      (isPreviousInOrbit_iff_eq_arTranslation sigma H D xn
        (positionEquiv sigma H D p)).1 hpxObj
    have hpy : HasIrreducibleMorphism
        (sigma.obj (positionEquiv sigma H D p))
        (sigma.obj (positionEquiv sigma H D y)) := by
      rw [hpEq]
      exact (D.arTranslation_incidence sigma xn
        (positionEquiv sigma H D y)).1 hyx
    exact (position_lt_iff sigma H D p y).1
      (HO.lt_of_irreducible hpy)
  · intro z hyz hzx hzLabel
    have hyzObj : positionEquiv sigma H D y <
        positionEquiv sigma H D z :=
      (position_lt_iff sigma H D y z).2 hyz
    have hzxObj : positionEquiv sigma H D z <
        positionEquiv sigma H D x :=
      (position_lt_iff sigma H D z x).2 hzx
    have hzOrbit : arOrbitLabel sigma H D (positionEquiv sigma H D z) =
        arOrbitLabel sigma H D (positionEquiv sigma H D y) := by
      simpa only [label_word] using hzLabel
    have hyzHeight : arHeight sigma D (positionEquiv sigma H D y) <
        arHeight sigma D (positionEquiv sigma H D z) :=
      (lt_iff_arHeight_lt_of_arOrbitLabel_eq sigma H D hzOrbit.symm).1
        hyzObj
    have hcross :=
      (lt_iff_seed_cross_height_le sigma H D hyx hzOrbit rfl).1 hzxObj
    omega

/-- Conversely, the middle-position rule selects an actual irreducible
arrow.  At a repeated target, the predecessor inequality forces the exact
height offset.  At a projective target, maximality of the middle occurrence
does the same job, including truncated injective boundaries. -/
theorem hasIrreducibleMorphism_of_isMiddle
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma)
    (y x : Fin (word sigma H D).length)
    (hyx : ARWord.IsMiddle
      (orbitGraph sigma H D) (word sigma H D) y x) :
    HasIrreducibleMorphism
      (sigma.obj (positionEquiv sigma H D y))
      (sigma.obj (positionEquiv sigma H D x)) := by
  letI := directedLinearOrder sigma H
  rcases hyx with ⟨hadj, hyx, hafter, hlast⟩
  have hyxObj : positionEquiv sigma H D y <
      positionEquiv sigma H D x :=
    (position_lt_iff sigma H D y x).2 hyx
  have hadjObj :
      HasOrientedOrbitArrow sigma H D
          (arOrbitLabel sigma H D (positionEquiv sigma H D y))
          (arOrbitLabel sigma H D (positionEquiv sigma H D x)) ∨
        HasOrientedOrbitArrow sigma H D
          (arOrbitLabel sigma H D (positionEquiv sigma H D x))
          (arOrbitLabel sigma H D (positionEquiv sigma H D y)) := by
    simpa only [orbitGraph, label_word] using hadj
  rcases hadjObj with hforward | hreverse
  · obtain ⟨u, v, huv, hu, hv⟩ := hforward
    have hYu : arOrbitLabel sigma H D (positionEquiv sigma H D y) =
        arOrbitLabel sigma H D u := hu.symm
    have hXv : arOrbitLabel sigma H D (positionEquiv sigma H D x) =
        arOrbitLabel sigma H D v := hv.symm
    apply (irreducible_same_orientation_iff_height_offset
      sigma H D huv hYu hXv).2
    have hUpper :=
      (lt_iff_seed_cross_height_le sigma H D huv hYu hXv).1 hyxObj
    by_cases hxProjective :
        Projective (sigma.obj (positionEquiv sigma H D x))
    · have hxHeight : arHeight sigma D (positionEquiv sigma H D x) = 0 :=
        (arHeight_eq_zero_iff_projective sigma H D
          (positionEquiv sigma H D x)).2 hxProjective
      apply Nat.le_antisymm hUpper
      by_contra hnot
      let n : ℕ := arHeight sigma D u - arHeight sigma D v
      have hvleu : arHeight sigma D v ≤ arHeight sigma D u := by omega
      have hnEq : n + arHeight sigma D v = arHeight sigma D u := by
        dsimp only [n]
        omega
      have hyn : arHeight sigma D (positionEquiv sigma H D y) < n := by
        omega
      have hnleY : n ≤
          arOrbitLength sigma H D (positionEquiv sigma H D y) := by
        rw [arOrbitLength_eq_of_arOrbitLabel_eq sigma H D hYu]
        exact (Nat.sub_le _ _).trans
          (arHeight_le_arOrbitLength sigma H D u)
      obtain ⟨z, hzOrbit, hzHeight⟩ :=
        (existsUnique_arOrbitLabel_eq_and_arHeight_eq sigma H D
          (positionEquiv sigma H D y) n hnleY).exists
      have hyzObj : positionEquiv sigma H D y < z :=
        (lt_iff_arHeight_lt_of_arOrbitLabel_eq sigma H D
          hzOrbit.symm).2 (by omega)
      let q : Fin (word sigma H D).length :=
        (positionEquiv sigma H D).symm z
      have hyq : y < q := by
        apply (position_lt_iff sigma H D y q).1
        simpa only [q, positionEquiv_symm_apply_apply] using hyzObj
      have hzxObj : z < positionEquiv sigma H D x :=
        (lt_iff_seed_cross_height_le sigma H D huv
          (hzOrbit.trans hYu) hXv).2 (by omega)
      have hqx : q < x := by
        apply (position_lt_iff sigma H D q x).1
        simpa only [q, positionEquiv_symm_apply_apply] using hzxObj
      apply hlast q hyq hqx
      simpa only [label_word, q, positionEquiv_symm_apply_apply] using hzOrbit
    · obtain ⟨p, hpx'⟩ :=
        (exists_previous_position_iff_not_projective sigma H D
          (positionEquiv sigma H D x)).2 hxProjective
      have hpx : ARWord.IsPrevious (word sigma H D) p x := by
        simpa only [positionEquiv_apply_symm_apply] using hpx'
      have hpxObj :=
        (isPrevious_word_iff_isPreviousInOrbit sigma H D p x).1 hpx
      have hpOrbitV : arOrbitLabel sigma H D (positionEquiv sigma H D p) =
          arOrbitLabel sigma H D v := hpxObj.2.1.trans hXv
      have hpHeight :=
        arHeight_eq_add_one_of_isPreviousInOrbit sigma H D hpxObj
      have hpyObj : positionEquiv sigma H D p <
          positionEquiv sigma H D y :=
        (position_lt_iff sigma H D p y).2 (hafter p hpx)
      have hLower :=
        (reverse_lt_iff_seed_cross_height_gt sigma H D huv
          hYu hpOrbitV).1 hpyObj
      omega
  · obtain ⟨u, v, huv, hu, hv⟩ := hreverse
    have hXu : arOrbitLabel sigma H D (positionEquiv sigma H D x) =
        arOrbitLabel sigma H D u := hu.symm
    have hYv : arOrbitLabel sigma H D (positionEquiv sigma H D y) =
        arOrbitLabel sigma H D v := hv.symm
    apply (irreducible_reverse_orientation_iff_height_offset
      sigma H D huv hXu hYv).2
    have hUpperStrict :=
      (reverse_lt_iff_seed_cross_height_gt sigma H D huv hXu hYv).1 hyxObj
    by_cases hxProjective :
        Projective (sigma.obj (positionEquiv sigma H D x))
    · have hxHeight : arHeight sigma D (positionEquiv sigma H D x) = 0 :=
        (arHeight_eq_zero_iff_projective sigma H D
          (positionEquiv sigma H D x)).2 hxProjective
      apply Nat.le_antisymm (by omega)
      by_contra hnot
      let n : ℕ := arHeight sigma D v - (arHeight sigma D u + 1)
      have hulev : arHeight sigma D u + 1 ≤ arHeight sigma D v := by
        omega
      have hnEq : n + arHeight sigma D u + 1 = arHeight sigma D v := by
        dsimp only [n]
        omega
      have hyn : arHeight sigma D (positionEquiv sigma H D y) < n := by
        omega
      have hnleY : n ≤
          arOrbitLength sigma H D (positionEquiv sigma H D y) := by
        rw [arOrbitLength_eq_of_arOrbitLabel_eq sigma H D hYv]
        exact (Nat.sub_le _ _).trans
          (arHeight_le_arOrbitLength sigma H D v)
      obtain ⟨z, hzOrbit, hzHeight⟩ :=
        (existsUnique_arOrbitLabel_eq_and_arHeight_eq sigma H D
          (positionEquiv sigma H D y) n hnleY).exists
      have hyzObj : positionEquiv sigma H D y < z :=
        (lt_iff_arHeight_lt_of_arOrbitLabel_eq sigma H D
          hzOrbit.symm).2 (by omega)
      let q : Fin (word sigma H D).length :=
        (positionEquiv sigma H D).symm z
      have hyq : y < q := by
        apply (position_lt_iff sigma H D y q).1
        simpa only [q, positionEquiv_symm_apply_apply] using hyzObj
      have hzxObj : z < positionEquiv sigma H D x :=
        (reverse_lt_iff_seed_cross_height_gt sigma H D huv
          hXu (hzOrbit.trans hYv)).2 (by omega)
      have hqx : q < x := by
        apply (position_lt_iff sigma H D q x).1
        simpa only [q, positionEquiv_symm_apply_apply] using hzxObj
      apply hlast q hyq hqx
      simpa only [label_word, q, positionEquiv_symm_apply_apply] using hzOrbit
    · obtain ⟨p, hpx'⟩ :=
        (exists_previous_position_iff_not_projective sigma H D
          (positionEquiv sigma H D x)).2 hxProjective
      have hpx : ARWord.IsPrevious (word sigma H D) p x := by
        simpa only [positionEquiv_apply_symm_apply] using hpx'
      have hpxObj :=
        (isPrevious_word_iff_isPreviousInOrbit sigma H D p x).1 hpx
      have hpOrbitU : arOrbitLabel sigma H D (positionEquiv sigma H D p) =
          arOrbitLabel sigma H D u := hpxObj.2.1.trans hXu
      have hpHeight :=
        arHeight_eq_add_one_of_isPreviousInOrbit sigma H D hpxObj
      have hpyObj : positionEquiv sigma H D p <
          positionEquiv sigma H D y :=
        (position_lt_iff sigma H D p y).2 (hafter p hpx)
      have hLower :=
        (lt_iff_seed_cross_height_le sigma H D huv
          hpOrbitU hYv).1 hpyObj
      omega

/-- Exact paper-facing word/arrow dictionary. -/
theorem isMiddle_iff_hasIrreducibleMorphism
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma)
    (y x : Fin (word sigma H D).length) :
    ARWord.IsMiddle (orbitGraph sigma H D) (word sigma H D) y x ↔
      HasIrreducibleMorphism
        (sigma.obj (positionEquiv sigma H D y))
        (sigma.obj (positionEquiv sigma H D x)) :=
  ⟨hasIrreducibleMorphism_of_isMiddle sigma H D y x,
    isMiddle_of_hasIrreducibleMorphism sigma H D y x⟩

/-! ## Structural properties for an explicit directed order -/

/-- Consecutive occurrences in one AR orbit differ by one in height for an
explicit directed order. -/
theorem arHeight_eq_add_one_of_isPreviousInOrbitFor
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (E : DirectedOrderChoice sigma) {p x : Iota}
    (hpx : letI := E.order
      IsPreviousInOrbitFor sigma H D p x) :
    arHeight sigma D x = arHeight sigma D p + 1 := by
  letI := E.order
  let HO : DirectedHomOrder sigma := E.directedHomOrder sigma
  have hxNonprojective : ¬ Projective (sigma.obj x) := by
    intro hxProjective
    rcases arReach_or_arReach_of_arOrbitLabel_eq sigma H D hpx.2.1 with
        hpxReach | hxpReach
    · exact hpx.1.ne
        (reflTransGen_arStep_eq_of_projective_target
          sigma D hxProjective hpxReach)
    · exact (not_le_of_gt hpx.1) (arReach_leFor sigma HO D hxpReach)
  let xn : sigma.NonprojectiveLabel := ⟨x, hxNonprojective⟩
  have hp : p = (D.arTranslation sigma xn).1 :=
    (isPreviousInOrbitFor_iff_eq_arTranslation
      sigma H HO D xn p).1 hpx
  have hheight := arHeight_translation sigma H D xn
  simpa only [xn, ← hp] using hheight

/-- Every adjacent pair of orbit labels has interior alternation in the AR
word of any explicitly supplied directed order. -/
theorem wordFor_hasInteriorAlternation
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (E : DirectedOrderChoice sigma) :
    ARWord.HasInteriorAlternation
      (orbitGraph sigma H D) (wordFor sigma H D E) := by
  letI := E.order
  let HO : DirectedHomOrder sigma := E.directedHomOrder sigma
  intro p x y z hpx hadj hpy hyx hpz hzx hzLabel
  have hpxObj : IsPreviousInOrbitFor sigma H D
      (positionEquivFor sigma H D E p)
      (positionEquivFor sigma H D E x) :=
    (isPrevious_wordFor_iff_isPreviousInOrbitFor
      sigma H D E p x).1 hpx
  have hpyObj : positionEquivFor sigma H D E p <
      positionEquivFor sigma H D E y :=
    (positionFor_lt_iff sigma H D E p y).2 hpy
  have hyxObj : positionEquivFor sigma H D E y <
      positionEquivFor sigma H D E x :=
    (positionFor_lt_iff sigma H D E y x).2 hyx
  have hpzObj : positionEquivFor sigma H D E p <
      positionEquivFor sigma H D E z :=
    (positionFor_lt_iff sigma H D E p z).2 hpz
  have hzxObj : positionEquivFor sigma H D E z <
      positionEquivFor sigma H D E x :=
    (positionFor_lt_iff sigma H D E z x).2 hzx
  have hxHeight : arHeight sigma D (positionEquivFor sigma H D E x) =
      arHeight sigma D (positionEquivFor sigma H D E p) + 1 :=
    arHeight_eq_add_one_of_isPreviousInOrbitFor sigma H D E hpxObj
  have hzOrbit :
      arOrbitLabel sigma H D (positionEquivFor sigma H D E z) =
        arOrbitLabel sigma H D (positionEquivFor sigma H D E y) := by
    simpa only [label_wordFor] using hzLabel
  have hadjObj :
      HasOrientedOrbitArrow sigma H D
          (arOrbitLabel sigma H D (positionEquivFor sigma H D E p))
          (arOrbitLabel sigma H D (positionEquivFor sigma H D E y)) ∨
        HasOrientedOrbitArrow sigma H D
          (arOrbitLabel sigma H D (positionEquivFor sigma H D E y))
          (arOrbitLabel sigma H D (positionEquivFor sigma H D E p)) := by
    simpa only [orbitGraph, label_wordFor] using hadj
  rcases hadjObj with hforward | hreverse
  · obtain ⟨u, v, huv, hu, hv⟩ := hforward
    have hpOrbitU :
        arOrbitLabel sigma H D (positionEquivFor sigma H D E p) =
          arOrbitLabel sigma H D u := hu.symm
    have hyOrbitV :
        arOrbitLabel sigma H D (positionEquivFor sigma H D E y) =
          arOrbitLabel sigma H D v := hv.symm
    have hxOrbitU :
        arOrbitLabel sigma H D (positionEquivFor sigma H D E x) =
          arOrbitLabel sigma H D u := hpxObj.2.1.symm.trans hu.symm
    have hzOrbitV :
        arOrbitLabel sigma H D (positionEquivFor sigma H D E z) =
          arOrbitLabel sigma H D v := hzOrbit.trans hv.symm
    have hyLower :=
      (lt_iff_seed_cross_height_leFor sigma H HO D
        huv hpOrbitU hyOrbitV).1 hpyObj
    have hyUpper :=
      (reverse_lt_iff_seed_cross_height_gtFor sigma H HO D
        huv hxOrbitU hyOrbitV).1 hyxObj
    have hzLower :=
      (lt_iff_seed_cross_height_leFor sigma H HO D
        huv hpOrbitU hzOrbitV).1 hpzObj
    have hzUpper :=
      (reverse_lt_iff_seed_cross_height_gtFor sigma H HO D
        huv hxOrbitU hzOrbitV).1 hzxObj
    apply (positionEquivFor sigma H D E).injective
    apply eq_of_arOrbitLabel_eq_of_arHeight_eq sigma H D hzOrbit
    omega
  · obtain ⟨u, v, huv, hu, hv⟩ := hreverse
    have hyOrbitU :
        arOrbitLabel sigma H D (positionEquivFor sigma H D E y) =
          arOrbitLabel sigma H D u := hu.symm
    have hpOrbitV :
        arOrbitLabel sigma H D (positionEquivFor sigma H D E p) =
          arOrbitLabel sigma H D v := hv.symm
    have hzOrbitU :
        arOrbitLabel sigma H D (positionEquivFor sigma H D E z) =
          arOrbitLabel sigma H D u := hzOrbit.trans hu.symm
    have hxOrbitV :
        arOrbitLabel sigma H D (positionEquivFor sigma H D E x) =
          arOrbitLabel sigma H D v := hpxObj.2.1.symm.trans hv.symm
    have hyLower :=
      (reverse_lt_iff_seed_cross_height_gtFor sigma H HO D
        huv hyOrbitU hpOrbitV).1 hpyObj
    have hyUpper :=
      (lt_iff_seed_cross_height_leFor sigma H HO D
        huv hyOrbitU hxOrbitV).1 hyxObj
    have hzLower :=
      (reverse_lt_iff_seed_cross_height_gtFor sigma H HO D
        huv hzOrbitU hpOrbitV).1 hpzObj
    have hzUpper :=
      (lt_iff_seed_cross_height_leFor sigma H HO D
        huv hzOrbitU hxOrbitV).1 hzxObj
    apply (positionEquivFor sigma H D E).injective
    apply eq_of_arOrbitLabel_eq_of_arHeight_eq sigma H D hzOrbit
    omega

/-- Within one translation orbit, every explicit directed order is exactly
the AR-height order. -/
theorem lt_iff_arHeight_lt_of_arOrbitLabel_eqFor
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (E : DirectedOrderChoice sigma) {x y : Iota}
    (horbit : arOrbitLabel sigma H D x = arOrbitLabel sigma H D y) :
    letI := E.order
    x < y ↔ arHeight sigma D x < arHeight sigma D y := by
  letI := E.order
  let HO : DirectedHomOrder sigma := E.directedHomOrder sigma
  constructor
  · intro hxy
    rcases arReach_or_arReach_of_arOrbitLabel_eq sigma H D horbit with
        hreach | hback
    · exact arHeight_lt_of_arReach_of_ne sigma H D hreach hxy.ne
    · exact False.elim ((not_le_of_gt hxy) (arReach_leFor sigma HO D hback))
  · intro hheight
    have hreach := arReach_of_arOrbitLabel_eq_of_arHeight_le
      sigma H D horbit hheight.le
    exact lt_of_le_of_ne (arReach_leFor sigma HO D hreach)
      (fun hxy ↦ by subst y; omega)

/-- In every adjacent two-label projection of an explicit-order AR word,
only its first and last runs may contain repeated letters. -/
theorem wordFor_hasOnlyBoundaryRepeatedRuns
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (E : DirectedOrderChoice sigma) :
    ARWord.HasOnlyBoundaryRepeatedRuns
      (orbitGraph sigma H D) (wordFor sigma H D E) := by
  letI := E.order
  let HO : DirectedHomOrder sigma := E.directedHomOrder sigma
  rw [ARWord.hasOnlyBoundaryRepeatedRuns_iff]
  intro a b hab x y hxy hxa hya hbetween
  by_contra hboundary
  push Not at hboundary
  obtain ⟨z, hzx, hzb⟩ := hboundary.1
  obtain ⟨w, hyw, hwb⟩ := hboundary.2
  have hzxObj : positionEquivFor sigma H D E z <
      positionEquivFor sigma H D E x :=
    (positionFor_lt_iff sigma H D E z x).2 hzx
  have hxyObj : positionEquivFor sigma H D E x <
      positionEquivFor sigma H D E y :=
    (positionFor_lt_iff sigma H D E x y).2 hxy
  have hywObj : positionEquivFor sigma H D E y <
      positionEquivFor sigma H D E w :=
    (positionFor_lt_iff sigma H D E y w).2 hyw
  have hxyOrbit :
      arOrbitLabel sigma H D (positionEquivFor sigma H D E x) =
        arOrbitLabel sigma H D (positionEquivFor sigma H D E y) := by
    simpa only [label_wordFor] using hxa.trans hya.symm
  have hxHeightLt :
      arHeight sigma D (positionEquivFor sigma H D E x) <
        arHeight sigma D (positionEquivFor sigma H D E y) :=
    (lt_iff_arHeight_lt_of_arOrbitLabel_eqFor
      sigma H D E hxyOrbit).1 hxyObj
  have hzOrbitB :
      arOrbitLabel sigma H D (positionEquivFor sigma H D E z) = b := by
    simpa only [label_wordFor] using hzb
  have hwOrbitB :
      arOrbitLabel sigma H D (positionEquivFor sigma H D E w) = b := by
    simpa only [label_wordFor] using hwb
  have hxOrbitA :
      arOrbitLabel sigma H D (positionEquivFor sigma H D E x) = a := by
    simpa only [label_wordFor] using hxa
  have hyOrbitA :
      arOrbitLabel sigma H D (positionEquivFor sigma H D E y) = a := by
    simpa only [label_wordFor] using hya
  have habObj :
      HasOrientedOrbitArrow sigma H D a b ∨
        HasOrientedOrbitArrow sigma H D b a := by
    simpa only [orbitGraph] using hab
  rcases habObj with habForward | habReverse
  · obtain ⟨u, v, huv, hu, hv⟩ := habForward
    have hxOrbitU :
        arOrbitLabel sigma H D (positionEquivFor sigma H D E x) =
          arOrbitLabel sigma H D u := hxOrbitA.trans hu.symm
    have hyOrbitU :
        arOrbitLabel sigma H D (positionEquivFor sigma H D E y) =
          arOrbitLabel sigma H D u := hyOrbitA.trans hu.symm
    have hzOrbitV :
        arOrbitLabel sigma H D (positionEquivFor sigma H D E z) =
          arOrbitLabel sigma H D v := hzOrbitB.trans hv.symm
    have hwOrbitV :
        arOrbitLabel sigma H D (positionEquivFor sigma H D E w) =
          arOrbitLabel sigma H D v := hwOrbitB.trans hv.symm
    have hzBefore :=
      (reverse_lt_iff_seed_cross_height_gtFor sigma H HO D
        huv hxOrbitU hzOrbitV).1 hzxObj
    have hyBeforeW :=
      (lt_iff_seed_cross_height_leFor sigma H HO D
        huv hyOrbitU hwOrbitV).1 hywObj
    let n : ℕ :=
      arHeight sigma D (positionEquivFor sigma H D E x) +
        arHeight sigma D v - arHeight sigma D u
    have huLe : arHeight sigma D u ≤
        arHeight sigma D (positionEquivFor sigma H D E x) +
          arHeight sigma D v := by
      omega
    have hnEq : n + arHeight sigma D u =
        arHeight sigma D (positionEquivFor sigma H D E x) +
          arHeight sigma D v := by
      exact Nat.sub_add_cancel huLe
    have hnLeW : n ≤ arHeight sigma D
        (positionEquivFor sigma H D E w) := by
      omega
    obtain ⟨tObj, htOrbitW, htHeight⟩ :=
      exists_arOrbitLabel_eq_arHeight_eq_of_le sigma H D
        (positionEquivFor sigma H D E w) n hnLeW
    let t : Fin (wordFor sigma H D E).length :=
      (positionEquivFor sigma H D E).symm tObj
    have htObj : positionEquivFor sigma H D E t = tObj := by
      simp only [t, positionEquivFor_symm_apply_apply]
    have htOrbitV : arOrbitLabel sigma H D tObj =
        arOrbitLabel sigma H D v := htOrbitW.trans hwOrbitV
    have hxtObj : positionEquivFor sigma H D E x < tObj := by
      apply (lt_iff_seed_cross_height_leFor sigma H HO D
        huv hxOrbitU htOrbitV).2
      rw [htHeight, hnEq]
    have htyObj : tObj < positionEquivFor sigma H D E y := by
      apply (reverse_lt_iff_seed_cross_height_gtFor sigma H HO D
        huv hyOrbitU htOrbitV).2
      rw [htHeight, hnEq]
      omega
    have hxt : x < t := by
      apply (positionFor_lt_iff sigma H D E x t).1
      simpa only [htObj] using hxtObj
    have hty : t < y := by
      apply (positionFor_lt_iff sigma H D E t y).1
      simpa only [htObj] using htyObj
    apply hbetween t hxt hty
    rw [label_wordFor, htObj, htOrbitV, hv]
  · obtain ⟨u, v, huv, hu, hv⟩ := habReverse
    have hzOrbitU :
        arOrbitLabel sigma H D (positionEquivFor sigma H D E z) =
          arOrbitLabel sigma H D u := hzOrbitB.trans hu.symm
    have hwOrbitU :
        arOrbitLabel sigma H D (positionEquivFor sigma H D E w) =
          arOrbitLabel sigma H D u := hwOrbitB.trans hu.symm
    have hxOrbitV :
        arOrbitLabel sigma H D (positionEquivFor sigma H D E x) =
          arOrbitLabel sigma H D v := hxOrbitA.trans hv.symm
    have hyOrbitV :
        arOrbitLabel sigma H D (positionEquivFor sigma H D E y) =
          arOrbitLabel sigma H D v := hyOrbitA.trans hv.symm
    have hzBefore :=
      (lt_iff_seed_cross_height_leFor sigma H HO D
        huv hzOrbitU hxOrbitV).1 hzxObj
    have hyBeforeW :=
      (reverse_lt_iff_seed_cross_height_gtFor sigma H HO D
        huv hwOrbitU hyOrbitV).1 hywObj
    let n : ℕ :=
      arHeight sigma D (positionEquivFor sigma H D E x) +
        arHeight sigma D u + 1 - arHeight sigma D v
    have hvLe : arHeight sigma D v ≤
        arHeight sigma D (positionEquivFor sigma H D E x) +
          arHeight sigma D u + 1 := by
      omega
    have hnEq : n + arHeight sigma D v =
        arHeight sigma D (positionEquivFor sigma H D E x) +
          arHeight sigma D u + 1 := by
      exact Nat.sub_add_cancel hvLe
    have hnLeW : n ≤ arHeight sigma D
        (positionEquivFor sigma H D E w) := by
      omega
    obtain ⟨tObj, htOrbitW, htHeight⟩ :=
      exists_arOrbitLabel_eq_arHeight_eq_of_le sigma H D
        (positionEquivFor sigma H D E w) n hnLeW
    let t : Fin (wordFor sigma H D E).length :=
      (positionEquivFor sigma H D E).symm tObj
    have htObj : positionEquivFor sigma H D E t = tObj := by
      simp only [t, positionEquivFor_symm_apply_apply]
    have htOrbitU : arOrbitLabel sigma H D tObj =
        arOrbitLabel sigma H D u := htOrbitW.trans hwOrbitU
    have hxtObj : positionEquivFor sigma H D E x < tObj := by
      apply (reverse_lt_iff_seed_cross_height_gtFor sigma H HO D
        huv htOrbitU hxOrbitV).2
      rw [htHeight, hnEq]
      omega
    have htyObj : tObj < positionEquivFor sigma H D E y := by
      apply (lt_iff_seed_cross_height_leFor sigma H HO D
        huv htOrbitU hyOrbitV).2
      rw [htHeight, hnEq]
      omega
    have hxt : x < t := by
      apply (positionFor_lt_iff sigma H D E x t).1
      simpa only [htObj] using hxtObj
    have hty : t < y := by
      apply (positionFor_lt_iff sigma H D E t y).1
      simpa only [htObj] using htyObj
    apply hbetween t hxt hty
    rw [label_wordFor, htObj, htOrbitU, hu]

/-- Every actual irreducible arrow is selected by the middle-position rule
in the AR word of an explicitly supplied directed order. -/
theorem isMiddle_of_hasIrreducibleMorphismFor
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (E : DirectedOrderChoice sigma)
    (y x : Fin (wordFor sigma H D E).length)
    (hyx : HasIrreducibleMorphism
      (sigma.obj (positionEquivFor sigma H D E y))
      (sigma.obj (positionEquivFor sigma H D E x))) :
    ARWord.IsMiddle (orbitGraph sigma H D)
      (wordFor sigma H D E) y x := by
  letI := E.order
  let HO : DirectedHomOrder sigma := E.directedHomOrder sigma
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [orbitGraph, label_wordFor] using
      (Or.inl ⟨positionEquivFor sigma H D E y,
        positionEquivFor sigma H D E x, hyx, rfl, rfl⟩ :
        HasOrientedOrbitArrow sigma H D
            (arOrbitLabel sigma H D (positionEquivFor sigma H D E y))
            (arOrbitLabel sigma H D (positionEquivFor sigma H D E x)) ∨
          HasOrientedOrbitArrow sigma H D
            (arOrbitLabel sigma H D (positionEquivFor sigma H D E x))
            (arOrbitLabel sigma H D (positionEquivFor sigma H D E y)))
  · exact (positionFor_lt_iff sigma H D E y x).1
      (HO.lt_of_irreducible hyx)
  · intro p hpx
    have hpxObj :=
      (isPrevious_wordFor_iff_isPreviousInOrbitFor
        sigma H D E p x).1 hpx
    have hxNonprojective :
        ¬ Projective (sigma.obj (positionEquivFor sigma H D E x)) :=
      (exists_isPreviousInOrbitFor_iff_not_projective sigma H HO D
        (positionEquivFor sigma H D E x)).1
        ⟨positionEquivFor sigma H D E p, hpxObj⟩
    let xn : sigma.NonprojectiveLabel :=
      ⟨positionEquivFor sigma H D E x, hxNonprojective⟩
    have hpEq : positionEquivFor sigma H D E p =
        (D.arTranslation sigma xn).1 :=
      (isPreviousInOrbitFor_iff_eq_arTranslation sigma H HO D xn
        (positionEquivFor sigma H D E p)).1 hpxObj
    have hpy : HasIrreducibleMorphism
        (sigma.obj (positionEquivFor sigma H D E p))
        (sigma.obj (positionEquivFor sigma H D E y)) := by
      rw [hpEq]
      exact (D.arTranslation_incidence sigma xn
        (positionEquivFor sigma H D E y)).1 hyx
    exact (positionFor_lt_iff sigma H D E p y).1
      (HO.lt_of_irreducible hpy)
  · intro z hyz hzx hzLabel
    have hyzObj : positionEquivFor sigma H D E y <
        positionEquivFor sigma H D E z :=
      (positionFor_lt_iff sigma H D E y z).2 hyz
    have hzxObj : positionEquivFor sigma H D E z <
        positionEquivFor sigma H D E x :=
      (positionFor_lt_iff sigma H D E z x).2 hzx
    have hzOrbit :
        arOrbitLabel sigma H D (positionEquivFor sigma H D E z) =
          arOrbitLabel sigma H D (positionEquivFor sigma H D E y) := by
      simpa only [label_wordFor] using hzLabel
    have hyzHeight :
        arHeight sigma D (positionEquivFor sigma H D E y) <
          arHeight sigma D (positionEquivFor sigma H D E z) :=
      (lt_iff_arHeight_lt_of_arOrbitLabel_eqFor
        sigma H D E hzOrbit.symm).1 hyzObj
    have hcross :=
      (lt_iff_seed_cross_height_leFor sigma H HO D hyx hzOrbit rfl).1
        hzxObj
    omega

/-- Conversely, the middle-position rule in an explicitly ordered AR word
selects an actual irreducible arrow. -/
theorem hasIrreducibleMorphism_of_isMiddleFor
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (E : DirectedOrderChoice sigma)
    (y x : Fin (wordFor sigma H D E).length)
    (hyx : ARWord.IsMiddle (orbitGraph sigma H D)
      (wordFor sigma H D E) y x) :
    HasIrreducibleMorphism
      (sigma.obj (positionEquivFor sigma H D E y))
      (sigma.obj (positionEquivFor sigma H D E x)) := by
  letI := E.order
  let HO : DirectedHomOrder sigma := E.directedHomOrder sigma
  rcases hyx with ⟨hadj, hyx, hafter, hlast⟩
  have hyxObj : positionEquivFor sigma H D E y <
      positionEquivFor sigma H D E x :=
    (positionFor_lt_iff sigma H D E y x).2 hyx
  have hadjObj :
      HasOrientedOrbitArrow sigma H D
          (arOrbitLabel sigma H D (positionEquivFor sigma H D E y))
          (arOrbitLabel sigma H D (positionEquivFor sigma H D E x)) ∨
        HasOrientedOrbitArrow sigma H D
          (arOrbitLabel sigma H D (positionEquivFor sigma H D E x))
          (arOrbitLabel sigma H D (positionEquivFor sigma H D E y)) := by
    simpa only [orbitGraph, label_wordFor] using hadj
  rcases hadjObj with hforward | hreverse
  · obtain ⟨u, v, huv, hu, hv⟩ := hforward
    have hYu :
        arOrbitLabel sigma H D (positionEquivFor sigma H D E y) =
          arOrbitLabel sigma H D u := hu.symm
    have hXv :
        arOrbitLabel sigma H D (positionEquivFor sigma H D E x) =
          arOrbitLabel sigma H D v := hv.symm
    apply (irreducible_same_orientation_iff_height_offset
      sigma H D huv hYu hXv).2
    have hUpper :=
      (lt_iff_seed_cross_height_leFor sigma H HO D
        huv hYu hXv).1 hyxObj
    by_cases hxProjective :
        Projective (sigma.obj (positionEquivFor sigma H D E x))
    · have hxHeight :
          arHeight sigma D (positionEquivFor sigma H D E x) = 0 :=
        (arHeight_eq_zero_iff_projective sigma H D
          (positionEquivFor sigma H D E x)).2 hxProjective
      apply Nat.le_antisymm hUpper
      by_contra hnot
      let n : ℕ := arHeight sigma D u - arHeight sigma D v
      have hvleu : arHeight sigma D v ≤ arHeight sigma D u := by omega
      have hnEq : n + arHeight sigma D v = arHeight sigma D u := by
        dsimp only [n]
        omega
      have hyn :
          arHeight sigma D (positionEquivFor sigma H D E y) < n := by
        omega
      have hnleY : n ≤
          arOrbitLength sigma H D (positionEquivFor sigma H D E y) := by
        rw [arOrbitLength_eq_of_arOrbitLabel_eq sigma H D hYu]
        exact (Nat.sub_le _ _).trans
          (arHeight_le_arOrbitLength sigma H D u)
      obtain ⟨z, hzOrbit, hzHeight⟩ :=
        (existsUnique_arOrbitLabel_eq_and_arHeight_eq sigma H D
          (positionEquivFor sigma H D E y) n hnleY).exists
      have hyzObj : positionEquivFor sigma H D E y < z :=
        (lt_iff_arHeight_lt_of_arOrbitLabel_eqFor sigma H D E
          hzOrbit.symm).2 (by omega)
      let q : Fin (wordFor sigma H D E).length :=
        (positionEquivFor sigma H D E).symm z
      have hyq : y < q := by
        apply (positionFor_lt_iff sigma H D E y q).1
        simpa only [q, positionEquivFor_symm_apply_apply] using hyzObj
      have hzxObj : z < positionEquivFor sigma H D E x :=
        (lt_iff_seed_cross_height_leFor sigma H HO D huv
          (hzOrbit.trans hYu) hXv).2 (by omega)
      have hqx : q < x := by
        apply (positionFor_lt_iff sigma H D E q x).1
        simpa only [q, positionEquivFor_symm_apply_apply] using hzxObj
      apply hlast q hyq hqx
      simpa only [label_wordFor, q,
        positionEquivFor_symm_apply_apply] using hzOrbit
    · obtain ⟨p, hpx'⟩ :=
        (exists_previous_positionFor_iff_not_projective sigma H D E
          (positionEquivFor sigma H D E x)).2 hxProjective
      have hpx : ARWord.IsPrevious (wordFor sigma H D E) p x := by
        simpa only [positionEquivFor_apply_symm_apply] using hpx'
      have hpxObj :=
        (isPrevious_wordFor_iff_isPreviousInOrbitFor
          sigma H D E p x).1 hpx
      have hpOrbitV :
          arOrbitLabel sigma H D (positionEquivFor sigma H D E p) =
            arOrbitLabel sigma H D v := hpxObj.2.1.trans hXv
      have hpHeight :=
        arHeight_eq_add_one_of_isPreviousInOrbitFor sigma H D E hpxObj
      have hpyObj : positionEquivFor sigma H D E p <
          positionEquivFor sigma H D E y :=
        (positionFor_lt_iff sigma H D E p y).2 (hafter p hpx)
      have hLower :=
        (reverse_lt_iff_seed_cross_height_gtFor sigma H HO D
          huv hYu hpOrbitV).1 hpyObj
      omega
  · obtain ⟨u, v, huv, hu, hv⟩ := hreverse
    have hXu :
        arOrbitLabel sigma H D (positionEquivFor sigma H D E x) =
          arOrbitLabel sigma H D u := hu.symm
    have hYv :
        arOrbitLabel sigma H D (positionEquivFor sigma H D E y) =
          arOrbitLabel sigma H D v := hv.symm
    apply (irreducible_reverse_orientation_iff_height_offset
      sigma H D huv hXu hYv).2
    have hUpperStrict :=
      (reverse_lt_iff_seed_cross_height_gtFor sigma H HO D
        huv hXu hYv).1 hyxObj
    by_cases hxProjective :
        Projective (sigma.obj (positionEquivFor sigma H D E x))
    · have hxHeight :
          arHeight sigma D (positionEquivFor sigma H D E x) = 0 :=
        (arHeight_eq_zero_iff_projective sigma H D
          (positionEquivFor sigma H D E x)).2 hxProjective
      apply Nat.le_antisymm (by omega)
      by_contra hnot
      let n : ℕ := arHeight sigma D v - (arHeight sigma D u + 1)
      have hulev : arHeight sigma D u + 1 ≤ arHeight sigma D v := by
        omega
      have hnEq : n + arHeight sigma D u + 1 = arHeight sigma D v := by
        dsimp only [n]
        omega
      have hyn :
          arHeight sigma D (positionEquivFor sigma H D E y) < n := by
        omega
      have hnleY : n ≤
          arOrbitLength sigma H D (positionEquivFor sigma H D E y) := by
        rw [arOrbitLength_eq_of_arOrbitLabel_eq sigma H D hYv]
        exact (Nat.sub_le _ _).trans
          (arHeight_le_arOrbitLength sigma H D v)
      obtain ⟨z, hzOrbit, hzHeight⟩ :=
        (existsUnique_arOrbitLabel_eq_and_arHeight_eq sigma H D
          (positionEquivFor sigma H D E y) n hnleY).exists
      have hyzObj : positionEquivFor sigma H D E y < z :=
        (lt_iff_arHeight_lt_of_arOrbitLabel_eqFor sigma H D E
          hzOrbit.symm).2 (by omega)
      let q : Fin (wordFor sigma H D E).length :=
        (positionEquivFor sigma H D E).symm z
      have hyq : y < q := by
        apply (positionFor_lt_iff sigma H D E y q).1
        simpa only [q, positionEquivFor_symm_apply_apply] using hyzObj
      have hzxObj : z < positionEquivFor sigma H D E x :=
        (reverse_lt_iff_seed_cross_height_gtFor sigma H HO D huv
          hXu (hzOrbit.trans hYv)).2 (by omega)
      have hqx : q < x := by
        apply (positionFor_lt_iff sigma H D E q x).1
        simpa only [q, positionEquivFor_symm_apply_apply] using hzxObj
      apply hlast q hyq hqx
      simpa only [label_wordFor, q,
        positionEquivFor_symm_apply_apply] using hzOrbit
    · obtain ⟨p, hpx'⟩ :=
        (exists_previous_positionFor_iff_not_projective sigma H D E
          (positionEquivFor sigma H D E x)).2 hxProjective
      have hpx : ARWord.IsPrevious (wordFor sigma H D E) p x := by
        simpa only [positionEquivFor_apply_symm_apply] using hpx'
      have hpxObj :=
        (isPrevious_wordFor_iff_isPreviousInOrbitFor
          sigma H D E p x).1 hpx
      have hpOrbitU :
          arOrbitLabel sigma H D (positionEquivFor sigma H D E p) =
            arOrbitLabel sigma H D u := hpxObj.2.1.trans hXu
      have hpHeight :=
        arHeight_eq_add_one_of_isPreviousInOrbitFor sigma H D E hpxObj
      have hpyObj : positionEquivFor sigma H D E p <
          positionEquivFor sigma H D E y :=
        (positionFor_lt_iff sigma H D E p y).2 (hafter p hpx)
      have hLower :=
        (lt_iff_seed_cross_height_leFor sigma H HO D
          huv hpOrbitU hYv).1 hpyObj
      omega

/-- Exact explicit-order AR-word/irreducible-arrow dictionary. -/
theorem isMiddle_iff_hasIrreducibleMorphismFor
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (E : DirectedOrderChoice sigma)
    (y x : Fin (wordFor sigma H D E).length) :
    ARWord.IsMiddle (orbitGraph sigma H D)
        (wordFor sigma H D E) y x ↔
      HasIrreducibleMorphism
        (sigma.obj (positionEquivFor sigma H D E y))
        (sigma.obj (positionEquivFor sigma H D E x)) :=
  ⟨hasIrreducibleMorphism_of_isMiddleFor sigma H D E y x,
    isMiddle_of_hasIrreducibleMorphismFor sigma H D E y x⟩


end OpConjecture.RepresentationDirected.DirectedAROrbit.OrderedARWord
