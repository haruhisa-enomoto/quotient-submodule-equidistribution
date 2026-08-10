import QuotientSubmoduleEquidistribution.RepresentationDirected.DirectedOrder
import QuotientSubmoduleEquidistribution.RepresentationTheory.FiniteARTranslationData
import Mathlib.Order.Preorder.Finite

/-!
# Directed Auslander--Reiten translation orbits

This file constructs the finite translation chains used to label the
Auslander--Reiten word of a representation-directed algebra.  A translation
step is oriented from `tau X` to `X`.  The directed order makes every such
step strict, while the finite AR-translation equivalence makes the step
relation deterministic in both directions away from its projective and
injective boundaries.

Consequently every label belongs to a unique finite chain from a projective
endpoint to an injective endpoint.  The projective endpoint and translation
height give injective coordinates on all labels.  The file also proves the
first structural clause of the manuscript's two-orbit lemma: no irreducible
arrow can join two vertices in the same translation orbit.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.RepresentationDirected.DirectedAROrbit

universe uR uIota

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {Iota : Type uIota} [Fintype Iota]
  (sigma : IndecomposableSkeleton.{uR, uIota, uR} R Iota)

abbrev ARData := sigma.FiniteARTranslationData

/-- One oriented translation edge, from `tau X` to `X`. -/
def ARStep (D : ARData sigma) (x y : Iota) : Prop :=
  ∃ z : sigma.NonprojectiveLabel,
    x = (D.arTranslation sigma z).1 ∧ y = z.1

omit [Fintype Iota] in
/-- A vertex has at most one immediate translation predecessor. -/
theorem arStep_leftUnique (D : ARData sigma) {x y z : Iota}
    (hxz : ARStep sigma D x z) (hyz : ARStep sigma D y z) : x = y := by
  obtain ⟨a, rfl, rfl⟩ := hxz
  obtain ⟨b, hxb, hb⟩ := hyz
  have hab : a = b := Subtype.ext hb
  subst b
  exact hxb.symm

omit [Fintype Iota] in
/-- A vertex has at most one immediate translation successor. -/
theorem arStep_rightUnique (D : ARData sigma) {x y z : Iota}
    (hxy : ARStep sigma D x y) (hxz : ARStep sigma D x z) : y = z := by
  obtain ⟨a, rfl, rfl⟩ := hxy
  obtain ⟨b, htaub, rfl⟩ := hxz
  have htau : D.arTranslation sigma a = D.arTranslation sigma b :=
    Subtype.ext htaub
  exact congrArg Subtype.val (D.arTranslation_injective sigma htau)

/-- For a relation with unique immediate predecessors, two paths with a
common target are comparable. -/
theorem reflTransGen_comparable_of_leftUnique
    {A : Type*} {r : A → A → Prop}
    (hleft : ∀ {a b c}, r a c → r b c → a = b)
    {a b c : A} (hab : Relation.ReflTransGen r a b)
    (hcb : Relation.ReflTransGen r c b) :
    Relation.ReflTransGen r a c ∨ Relation.ReflTransGen r c a := by
  induction hab with
  | refl => exact Or.inr hcb
  | tail hxy hyz ih =>
      rcases Relation.ReflTransGen.cases_tail hcb with h | ⟨w, hcw, hwz⟩
      · subst c
        exact Or.inl (Relation.ReflTransGen.tail hxy hyz)
      · have hw := hleft hwz hyz
        subst w
        exact ih hcw

/-- Dual common-source comparability for a relation with unique immediate
successors. -/
theorem reflTransGen_comparable_of_rightUnique
    {A : Type*} {r : A → A → Prop}
    (hright : ∀ {a b c}, r a b → r a c → b = c)
    {a b c : A} (hab : Relation.ReflTransGen r a b)
    (hac : Relation.ReflTransGen r a c) :
    Relation.ReflTransGen r b c ∨ Relation.ReflTransGen r c b := by
  have hleft : ∀ {a b c}, Function.swap r a c →
      Function.swap r b c → a = b := by
    intro a b c hca hcb
    exact hright hca hcb
  rcases reflTransGen_comparable_of_leftUnique
      (r := Function.swap r) (a := b) (b := a) (c := c)
      hleft hab.swap hac.swap with
      hbc | hcb
  · exact Or.inr hbc.swap
  · exact Or.inl hcb.swap

omit [Fintype Iota] in
/-- A translation path ending at a projective label is necessarily
reflexive. -/
theorem reflTransGen_arStep_eq_of_projective_target
    (D : ARData sigma) {x p : Iota} (hp : Projective (sigma.obj p))
    (hxp : Relation.ReflTransGen (ARStep sigma D) x p) : x = p := by
  rcases Relation.ReflTransGen.cases_tail hxp with h | ⟨y, _, hyp⟩
  · exact h.symm
  · obtain ⟨z, _, hzp⟩ := hyp
    subst p
    exact (z.2 hp).elim

omit [Fintype Iota] in
/-- A translation path starting at an injective label is necessarily
reflexive. -/
theorem reflTransGen_arStep_eq_of_injective_source
    (D : ARData sigma) {i x : Iota} (hi : Injective (sigma.obj i))
    (hix : Relation.ReflTransGen (ARStep sigma D) i x) : x = i := by
  rcases Relation.ReflTransGen.cases_head hix with h | ⟨y, hiy, _⟩
  · exact h.symm
  · obtain ⟨z, hiz, _⟩ := hiy
    have hninj : ¬ Injective (sigma.obj (D.arTranslation sigma z).1) :=
      (D.arTranslation sigma z).2
    rw [hiz] at hi
    exact (hninj hi).elim

omit [Fintype Iota] in
/-- AR translation strictly decreases the directed Hom order. -/
theorem arTranslation_lt
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (z : sigma.NonprojectiveLabel) :
    letI := directedLinearOrder sigma H
    (D.arTranslation sigma z).1 < z.1 := by
  letI := directedLinearOrder sigma H
  let HO : DirectedHomOrder sigma :=
    DirectedHomOrder.of_acyclicNonzeroNonisomorphisms sigma H
  let A := D.chosenRightAR sigma z
  let t : A.index :=
    Classical.choice (DirectedHomOrder.chosenRightAR_index_nonempty D z)
  let e : Iota := A.label t
  have hez : HasIrreducibleMorphism (sigma.obj e) (sigma.obj z.1) :=
    (A.summandIrreducibleCorrespondence e).1 ⟨t, rfl⟩
  have htaue : HasIrreducibleMorphism
      (sigma.obj (D.arTranslation sigma z).1) (sigma.obj e) :=
    (D.arTranslation_incidence sigma z e).1 hez
  exact (HO.lt_of_irreducible htaue).trans (HO.lt_of_irreducible hez)

omit [Fintype Iota] in
theorem arStep_lt
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) {x y : Iota} (hxy : ARStep sigma D x y) :
    letI := directedLinearOrder sigma H
    x < y := by
  letI := directedLinearOrder sigma H
  obtain ⟨z, rfl, rfl⟩ := hxy
  exact arTranslation_lt sigma H D z

omit [Fintype Iota] in
/-- Translation reachability is monotone in the directed order. -/
theorem arReach_le
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) {x y : Iota}
    (hxy : Relation.ReflTransGen (ARStep sigma D) x y) :
    letI := directedLinearOrder sigma H
    x ≤ y := by
  letI := directedLinearOrder sigma H
  induction hxy with
  | refl => exact le_rfl
  | tail _ hyz ih => exact ih.trans (arStep_lt sigma H D hyz).le

/-- The labels obtained by repeatedly applying AR translation. -/
def ARAncestors (D : ARData sigma) (x : Iota) : Set Iota :=
  {p | Relation.ReflTransGen (ARStep sigma D) p x}

omit [Fintype Iota] in
theorem arAncestors_mono (D : ARData sigma) {x y : Iota}
    (hxy : Relation.ReflTransGen (ARStep sigma D) x y) :
    ARAncestors sigma D x ⊆ ARAncestors sigma D y := fun _ hpx ↦
  hpx.trans hxy

omit [Fintype Iota] in
/-- The ancestors of a nonprojective label are the label itself together
with the ancestors of its translate. -/
theorem arAncestors_translation (D : ARData sigma)
    (z : sigma.NonprojectiveLabel) :
    ARAncestors sigma D z.1 =
      insert z.1 (ARAncestors sigma D (D.arTranslation sigma z).1) := by
  ext p
  constructor
  · intro hp
    rcases Relation.ReflTransGen.cases_tail hp with h | ⟨c, hpc, hcz⟩
    · exact Set.mem_insert_iff.mpr (Or.inl h.symm)
    · have hc : c = (D.arTranslation sigma z).1 :=
        arStep_leftUnique sigma D hcz ⟨z, rfl, rfl⟩
      exact Set.mem_insert_iff.mpr (Or.inr (hc ▸ hpc))
  · intro hp
    rcases Set.mem_insert_iff.mp hp with rfl | hp
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.tail hp ⟨z, rfl, rfl⟩

omit [Fintype Iota] in
theorem not_mem_arAncestors_arTranslation
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (z : sigma.NonprojectiveLabel) :
    z.1 ∉ ARAncestors sigma D (D.arTranslation sigma z).1 := by
  letI := directedLinearOrder sigma H
  intro hz
  have hle : z.1 ≤ (D.arTranslation sigma z).1 := arReach_le sigma H D hz
  exact (not_le_of_gt (arTranslation_lt sigma H D z)) hle

/-- Translation depth measured by the finite ancestor set. -/
def arHeight (D : ARData sigma) (x : Iota) : ℕ :=
  (ARAncestors sigma D x).ncard - 1

theorem ncard_arAncestors_translation
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (z : sigma.NonprojectiveLabel) :
    (ARAncestors sigma D z.1).ncard =
      (ARAncestors sigma D (D.arTranslation sigma z).1).ncard + 1 := by
  rw [arAncestors_translation sigma D z,
    Set.ncard_insert_of_notMem
      (not_mem_arAncestors_arTranslation sigma H D z)]

theorem arHeight_translation
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (z : sigma.NonprojectiveLabel) :
    arHeight sigma D z.1 =
      arHeight sigma D (D.arTranslation sigma z).1 + 1 := by
  have hcard := ncard_arAncestors_translation sigma H D z
  have hpos : 0 < (ARAncestors sigma D
      (D.arTranslation sigma z).1).ncard :=
    (Set.ncard_pos (s := ARAncestors sigma D
      (D.arTranslation sigma z).1)).mpr
      ⟨(D.arTranslation sigma z).1, Relation.ReflTransGen.refl⟩
  simp only [arHeight]
  omega

omit [Fintype Iota] in
theorem arAncestors_eq_singleton_of_projective
    (D : ARData sigma) {p : Iota} (hp : Projective (sigma.obj p)) :
    ARAncestors sigma D p = {p} := by
  ext x
  constructor
  · intro hxp
    exact Set.mem_singleton_iff.mpr
      (reflTransGen_arStep_eq_of_projective_target sigma D hp hxp)
  · intro hxp
    simpa only [Set.mem_singleton_iff] using hxp ▸
      (Relation.ReflTransGen.refl :
        Relation.ReflTransGen (ARStep sigma D) p p)

omit [Fintype Iota] in
theorem arHeight_eq_zero_of_projective
    (D : ARData sigma) {p : Iota} (hp : Projective (sigma.obj p)) :
    arHeight sigma D p = 0 := by
  simp [arHeight, arAncestors_eq_singleton_of_projective sigma D hp]

theorem ncard_arAncestors_eq_arHeight_add_one
    (D : ARData sigma) (x : Iota) :
    (ARAncestors sigma D x).ncard = arHeight sigma D x + 1 := by
  have hpos : 0 < (ARAncestors sigma D x).ncard :=
    (Set.ncard_pos (s := ARAncestors sigma D x)).mpr
      ⟨x, Relation.ReflTransGen.refl⟩
  simp only [arHeight]
  omega

theorem eq_of_arReach_of_arHeight_eq
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) {x y : Iota}
    (hxy : Relation.ReflTransGen (ARStep sigma D) x y)
    (hheight : arHeight sigma D x = arHeight sigma D y) : x = y := by
  have hcard : (ARAncestors sigma D x).ncard =
      (ARAncestors sigma D y).ncard := by
    rw [ncard_arAncestors_eq_arHeight_add_one sigma D x,
      ncard_arAncestors_eq_arHeight_add_one sigma D y, hheight]
  have hsets : ARAncestors sigma D x = ARAncestors sigma D y :=
    Set.eq_of_subset_of_ncard_le (arAncestors_mono sigma D hxy) hcard.ge
  have hyx : Relation.ReflTransGen (ARStep sigma D) y x := by
    change y ∈ ARAncestors sigma D x
    rw [hsets]
    exact Relation.ReflTransGen.refl
  letI := directedLinearOrder sigma H
  exact le_antisymm (arReach_le sigma H D hxy) (arReach_le sigma H D hyx)

theorem arHeight_le_of_arReach
    (D : ARData sigma) {x y : Iota}
    (hxy : Relation.ReflTransGen (ARStep sigma D) x y) :
    arHeight sigma D x ≤ arHeight sigma D y := by
  have hcard := Set.ncard_le_ncard (arAncestors_mono sigma D hxy)
  rw [ncard_arAncestors_eq_arHeight_add_one sigma D x,
    ncard_arAncestors_eq_arHeight_add_one sigma D y] at hcard
  omega

theorem arHeight_lt_of_arReach_of_ne
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) {x y : Iota}
    (hxy : Relation.ReflTransGen (ARStep sigma D) x y) (hne : x ≠ y) :
    arHeight sigma D x < arHeight sigma D y := by
  have hle := arHeight_le_of_arReach sigma D hxy
  have hheight : arHeight sigma D x ≠ arHeight sigma D y := fun h ↦
    hne (eq_of_arReach_of_arHeight_eq sigma H D hxy h)
  omega

/-- Every label has a projective ancestor in its finite translation chain. -/
theorem exists_projective_ancestor
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (x : Iota) :
    ∃ p : Iota, Projective (sigma.obj p) ∧
      Relation.ReflTransGen (ARStep sigma D) p x := by
  letI := directedLinearOrder sigma H
  classical
  let ancestors : Set Iota :=
    {p | Relation.ReflTransGen (ARStep sigma D) p x}
  have hx : x ∈ ancestors := Relation.ReflTransGen.refl
  obtain ⟨p, hp, hpmin⟩ :=
    Set.Finite.exists_minimal (Set.toFinite ancestors) ⟨x, hx⟩
  refine ⟨p, ?_, hp⟩
  by_contra hproj
  let z : sigma.NonprojectiveLabel := ⟨p, hproj⟩
  let q : Iota := (D.arTranslation sigma z).1
  have hqpStep : ARStep sigma D q p := ⟨z, rfl, rfl⟩
  have hqp : q < p := arTranslation_lt sigma H D z
  have hq : q ∈ ancestors :=
    Relation.ReflTransGen.head hqpStep hp
  exact (not_le_of_gt hqp) (hpmin hq hqp.le)

omit [Fintype Iota] in
/-- The projective ancestor of a finite translation chain is unique. -/
theorem projective_ancestor_unique
    (D : ARData sigma) {x p q : Iota}
    (hp : Projective (sigma.obj p))
    (hq : Projective (sigma.obj q))
    (hpx : Relation.ReflTransGen (ARStep sigma D) p x)
    (hqx : Relation.ReflTransGen (ARStep sigma D) q x) : p = q := by
  rcases reflTransGen_comparable_of_leftUnique
      (r := ARStep sigma D) (a := p) (b := x) (c := q)
      (fun hac hbc ↦ arStep_leftUnique sigma D hac hbc) hpx hqx with hpq | hqp
  · exact reflTransGen_arStep_eq_of_projective_target sigma D hq hpq
  · exact (reflTransGen_arStep_eq_of_projective_target sigma D hp hqp).symm

/-- A translation orbit is labelled by its unique projective endpoint. -/
def ProjectiveLabel := {p : Iota // Projective (sigma.obj p)}

/-- The projective endpoint of the translation chain containing `x`. -/
def arOrbitLabel
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (x : Iota) : ProjectiveLabel sigma :=
  ⟨(exists_projective_ancestor sigma H D x).choose,
    (exists_projective_ancestor sigma H D x).choose_spec.1⟩

theorem arOrbitLabel_reaches
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (x : Iota) :
    Relation.ReflTransGen (ARStep sigma D) (arOrbitLabel sigma H D x).1 x :=
  (exists_projective_ancestor sigma H D x).choose_spec.2

theorem arOrbitLabel_eq_of_projective_ancestor
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) {p x : Iota}
    (hp : Projective (sigma.obj p))
    (hpx : Relation.ReflTransGen (ARStep sigma D) p x) :
    arOrbitLabel sigma H D x = ⟨p, hp⟩ := by
  apply Subtype.ext
  exact projective_ancestor_unique sigma D
    (arOrbitLabel sigma H D x).2 hp
    (arOrbitLabel_reaches sigma H D x) hpx

theorem arOrbitLabel_eq_self_of_projective
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) {p : Iota} (hp : Projective (sigma.obj p)) :
    arOrbitLabel sigma H D p = ⟨p, hp⟩ :=
  arOrbitLabel_eq_of_projective_ancestor sigma H D hp
    Relation.ReflTransGen.refl

/-- Every projective endpoint occurs as an orbit label. -/
theorem arOrbitLabel_surjective
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) :
    Function.Surjective (arOrbitLabel sigma H D) := by
  intro p
  exact ⟨p.1, arOrbitLabel_eq_self_of_projective sigma H D p.2⟩

theorem arOrbitLabel_eq_of_reaches
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) {x y : Iota}
    (hxy : Relation.ReflTransGen (ARStep sigma D) x y) :
    arOrbitLabel sigma H D x = arOrbitLabel sigma H D y := by
  apply Subtype.ext
  exact projective_ancestor_unique sigma D
    (arOrbitLabel sigma H D x).2 (arOrbitLabel sigma H D y).2
    ((arOrbitLabel_reaches sigma H D x).trans hxy)
    (arOrbitLabel_reaches sigma H D y)

theorem arOrbitLabel_eq_of_arStep
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) {x y : Iota} (hxy : ARStep sigma D x y) :
    arOrbitLabel sigma H D x = arOrbitLabel sigma H D y :=
  arOrbitLabel_eq_of_reaches sigma H D
    (Relation.ReflTransGen.tail Relation.ReflTransGen.refl hxy)

theorem arOrbitLabel_translation
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (z : sigma.NonprojectiveLabel) :
    arOrbitLabel sigma H D (D.arTranslation sigma z).1 =
      arOrbitLabel sigma H D z.1 :=
  arOrbitLabel_eq_of_arStep sigma H D ⟨z, rfl, rfl⟩

/-- Projective root and translation depth are injective coordinates on the
finite AR translation chains. -/
theorem eq_of_arOrbitLabel_eq_of_arHeight_eq
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) {x y : Iota}
    (horbit : arOrbitLabel sigma H D x = arOrbitLabel sigma H D y)
    (hheight : arHeight sigma D x = arHeight sigma D y) : x = y := by
  have hrootx := arOrbitLabel_reaches sigma H D x
  have hrooty : Relation.ReflTransGen (ARStep sigma D)
      (arOrbitLabel sigma H D x).1 y := by
    simpa only [horbit] using arOrbitLabel_reaches sigma H D y
  rcases reflTransGen_comparable_of_rightUnique
      (r := ARStep sigma D)
      (fun hab hac ↦ arStep_rightUnique sigma D hab hac)
      hrootx hrooty with hxy | hyx
  · exact eq_of_arReach_of_arHeight_eq sigma H D hxy hheight
  · exact (eq_of_arReach_of_arHeight_eq sigma H D hyx hheight.symm).symm

/-- Height zero is exactly the projective boundary of the translation
chains. -/
theorem arHeight_eq_zero_iff_projective
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (x : Iota) :
    arHeight sigma D x = 0 ↔ Projective (sigma.obj x) := by
  constructor
  · intro hx
    let p := arOrbitLabel sigma H D x
    have hpHeight : arHeight sigma D p.1 = 0 :=
      arHeight_eq_zero_of_projective sigma D p.2
    have hpOrbit : arOrbitLabel sigma H D p.1 =
        arOrbitLabel sigma H D x :=
      arOrbitLabel_eq_of_reaches sigma H D
        (arOrbitLabel_reaches sigma H D x)
    have hpx : p.1 = x := eq_of_arOrbitLabel_eq_of_arHeight_eq
      sigma H D hpOrbit (hpHeight.trans hx.symm)
    rw [← hpx]
    exact p.2
  · exact arHeight_eq_zero_of_projective sigma D

/-- Positive height is exactly the nonprojective part of a translation
chain. -/
theorem arHeight_pos_iff_nonprojective
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (x : Iota) :
    0 < arHeight sigma D x ↔ ¬ Projective (sigma.obj x) := by
  rw [Nat.pos_iff_ne_zero, ne_eq,
    arHeight_eq_zero_iff_projective sigma H D x]

/-- Within one translation orbit, the height order is exactly translation
reachability. -/
theorem arReach_of_arOrbitLabel_eq_of_arHeight_le
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) {x y : Iota}
    (horbit : arOrbitLabel sigma H D x = arOrbitLabel sigma H D y)
    (hheight : arHeight sigma D x ≤ arHeight sigma D y) :
    Relation.ReflTransGen (ARStep sigma D) x y := by
  have hrootx := arOrbitLabel_reaches sigma H D x
  have hrooty : Relation.ReflTransGen (ARStep sigma D)
      (arOrbitLabel sigma H D x).1 y := by
    simpa only [horbit] using arOrbitLabel_reaches sigma H D y
  rcases reflTransGen_comparable_of_rightUnique
      (r := ARStep sigma D)
      (fun hab hac ↦ arStep_rightUnique sigma D hab hac)
      hrootx hrooty with hxy | hyx
  · exact hxy
  · have hyxHeight := arHeight_le_of_arReach sigma D hyx
    have heqHeight : arHeight sigma D x = arHeight sigma D y :=
      le_antisymm hheight hyxHeight
    have heq := eq_of_arOrbitLabel_eq_of_arHeight_eq sigma H D horbit heqHeight
    subst y
    exact Relation.ReflTransGen.refl

/-- Two vertices with the same projective orbit label are comparable by
translation reachability. -/
theorem arReach_or_arReach_of_arOrbitLabel_eq
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) {x y : Iota}
    (horbit : arOrbitLabel sigma H D x = arOrbitLabel sigma H D y) :
    Relation.ReflTransGen (ARStep sigma D) x y ∨
      Relation.ReflTransGen (ARStep sigma D) y x := by
  have hrootx := arOrbitLabel_reaches sigma H D x
  have hrooty : Relation.ReflTransGen (ARStep sigma D)
      (arOrbitLabel sigma H D x).1 y := by
    simpa only [horbit] using arOrbitLabel_reaches sigma H D y
  exact reflTransGen_comparable_of_rightUnique
    (r := ARStep sigma D)
    (fun hab hac ↦ arStep_rightUnique sigma D hab hac)
    hrootx hrooty

/-- Translation reachability is exactly equality of orbit labels together
with comparison of translation heights. -/
theorem arReach_iff_arOrbitLabel_eq_and_arHeight_le
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) {x y : Iota} :
    Relation.ReflTransGen (ARStep sigma D) x y ↔
      arOrbitLabel sigma H D x = arOrbitLabel sigma H D y ∧
        arHeight sigma D x ≤ arHeight sigma D y := by
  constructor
  · intro hxy
    exact ⟨arOrbitLabel_eq_of_reaches sigma H D hxy,
      arHeight_le_of_arReach sigma D hxy⟩
  · rintro ⟨horbit, hheight⟩
    exact arReach_of_arOrbitLabel_eq_of_arHeight_le
      sigma H D horbit hheight

/-- Every integer height between zero and a vertex occurs exactly once on
the translation chain leading to that vertex.  This theorem records the
existence part; uniqueness follows from the orbit-label/height coordinates. -/
theorem exists_arReach_of_arHeight_eq
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (y : Iota) (n : ℕ)
    (hn : n ≤ arHeight sigma D y) :
    ∃ x : Iota,
      Relation.ReflTransGen (ARStep sigma D) x y ∧
        arHeight sigma D x = n := by
  induction hheight : arHeight sigma D y using Nat.strong_induction_on
      generalizing y n with
  | h m ih =>
      by_cases hnm : n = m
      · exact ⟨y, Relation.ReflTransGen.refl,
          hheight.trans hnm.symm⟩
      · have hnmle : n ≤ m := by simpa only [hheight] using hn
        have hnlt : n < m := lt_of_le_of_ne hnmle hnm
        have hmpos : 0 < m := (Nat.zero_le n).trans_lt hnlt
        have hypos : 0 < arHeight sigma D y := by
          simpa only [hheight] using hmpos
        let z : sigma.NonprojectiveLabel :=
          ⟨y, (arHeight_pos_iff_nonprojective sigma H D y).mp hypos⟩
        have htau := arHeight_translation sigma H D z
        have hmTau :
            m = arHeight sigma D (D.arTranslation sigma z).1 + 1 := by
          calc
            m = arHeight sigma D y := hheight.symm
            _ = arHeight sigma D (D.arTranslation sigma z).1 + 1 := by
              simpa only [z] using htau
        have htauLt : arHeight sigma D (D.arTranslation sigma z).1 < m := by
          omega
        have hnTau : n ≤ arHeight sigma D (D.arTranslation sigma z).1 := by
          omega
        obtain ⟨x, hx, hxHeight⟩ :=
          ih (arHeight sigma D (D.arTranslation sigma z).1) htauLt
            (D.arTranslation sigma z).1 n hnTau rfl
        exact ⟨x, Relation.ReflTransGen.tail hx ⟨z, rfl, rfl⟩,
          hxHeight⟩

/-- The vertex of a prescribed height on a translation chain is unique. -/
theorem existsUnique_arReach_of_arHeight_eq
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (y : Iota) (n : ℕ)
    (hn : n ≤ arHeight sigma D y) :
    ∃! x : Iota,
      Relation.ReflTransGen (ARStep sigma D) x y ∧
        arHeight sigma D x = n := by
  obtain ⟨x, hxReach, hxHeight⟩ :=
    exists_arReach_of_arHeight_eq sigma H D y n hn
  refine ⟨x, ⟨hxReach, hxHeight⟩, ?_⟩
  intro z hz
  exact eq_of_arOrbitLabel_eq_of_arHeight_eq sigma H D
    ((arOrbitLabel_eq_of_reaches sigma H D hz.1).trans
      (arOrbitLabel_eq_of_reaches sigma H D hxReach).symm)
    (hz.2.trans hxHeight.symm)

/-- `p` is the immediately preceding member of the translation orbit of
`x` in the directed linear order. -/
def IsPreviousInOrbit
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (p x : Iota) : Prop :=
  letI := directedLinearOrder sigma H
  p < x ∧
    arOrbitLabel sigma H D p = arOrbitLabel sigma H D x ∧
    ∀ z : Iota, p < z → z < x →
      arOrbitLabel sigma H D z ≠ arOrbitLabel sigma H D x

/-- An immediate previous member of an orbit is unique. -/
theorem isPreviousInOrbit_unique
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) {p q x : Iota}
    (hp : IsPreviousInOrbit sigma H D p x)
    (hq : IsPreviousInOrbit sigma H D q x) : p = q := by
  letI := directedLinearOrder sigma H
  rcases lt_trichotomy p q with hpq | hpq | hqp
  · exact False.elim (hp.2.2 q hpq hq.1 hq.2.1)
  · exact hpq
  · exact False.elim (hq.2.2 p hqp hp.1 hp.2.1)

/-- For a nonprojective vertex, its AR translate is the immediately
preceding occurrence of its orbit label. -/
theorem arTranslation_isPreviousInOrbit
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (z : sigma.NonprojectiveLabel) :
    IsPreviousInOrbit sigma H D (D.arTranslation sigma z).1 z.1 := by
  letI := directedLinearOrder sigma H
  refine ⟨arTranslation_lt sigma H D z,
    arOrbitLabel_translation sigma H D z, ?_⟩
  intro y htauy hyz hyOrbit
  have htauOrbit :
      arOrbitLabel sigma H D (D.arTranslation sigma z).1 =
        arOrbitLabel sigma H D y :=
    (arOrbitLabel_translation sigma H D z).trans hyOrbit.symm
  rcases arReach_or_arReach_of_arOrbitLabel_eq sigma H D htauOrbit with
      htauReach | hyReach
  · rcases Relation.ReflTransGen.cases_head htauReach with
      hEq | ⟨a, htaua, hay⟩
    · subst y
      exact (lt_irrefl _ htauy).elim
    · have ha : a = z.1 :=
        arStep_rightUnique sigma D htaua ⟨z, rfl, rfl⟩
      subst a
      exact (not_le_of_gt hyz) (arReach_le sigma H D hay)
  · exact (not_le_of_gt htauy) (arReach_le sigma H D hyReach)

/-- A vertex has a preceding occurrence of its orbit label exactly when it
is nonprojective. -/
theorem exists_isPreviousInOrbit_iff_not_projective
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (x : Iota) :
    (∃ p : Iota, IsPreviousInOrbit sigma H D p x) ↔
      ¬ Projective (sigma.obj x) := by
  letI := directedLinearOrder sigma H
  constructor
  · rintro ⟨p, hp⟩ hprojective
    rcases arReach_or_arReach_of_arOrbitLabel_eq sigma H D hp.2.1 with
        hpx | hxp
    · exact hp.1.ne
        (reflTransGen_arStep_eq_of_projective_target
          sigma D hprojective hpx)
    · exact (not_le_of_gt hp.1) (arReach_le sigma H D hxp)
  · intro hprojective
    let z : sigma.NonprojectiveLabel := ⟨x, hprojective⟩
    exact ⟨(D.arTranslation sigma z).1,
      arTranslation_isPreviousInOrbit sigma H D z⟩

/-- The preceding occurrence at a nonprojective vertex is literally its AR
translate. -/
theorem isPreviousInOrbit_iff_eq_arTranslation
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (z : sigma.NonprojectiveLabel) (p : Iota) :
    IsPreviousInOrbit sigma H D p z.1 ↔
      p = (D.arTranslation sigma z).1 := by
  constructor
  · intro hp
    exact isPreviousInOrbit_unique sigma H D hp
      (arTranslation_isPreviousInOrbit sigma H D z)
  · rintro rfl
    exact arTranslation_isPreviousInOrbit sigma H D z

theorem arReach_of_arOrbitLabel_eq_of_irreducible
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) {x y : Iota}
    (horbit : arOrbitLabel sigma H D x = arOrbitLabel sigma H D y)
    (hxy : HasIrreducibleMorphism (sigma.obj x) (sigma.obj y)) :
    Relation.ReflTransGen (ARStep sigma D) x y := by
  letI := directedLinearOrder sigma H
  let HO : DirectedHomOrder sigma :=
    DirectedHomOrder.of_acyclicNonzeroNonisomorphisms sigma H
  have hlt : x < y := HO.lt_of_irreducible hxy
  have hrootx := arOrbitLabel_reaches sigma H D x
  have hrooty : Relation.ReflTransGen (ARStep sigma D)
      (arOrbitLabel sigma H D x).1 y := by
    simpa only [horbit] using arOrbitLabel_reaches sigma H D y
  rcases reflTransGen_comparable_of_rightUnique
      (r := ARStep sigma D)
      (fun hab hac ↦ arStep_rightUnique sigma D hab hac)
      hrootx hrooty with hreach | hback
  · exact hreach
  · exact (not_le_of_gt hlt (arReach_le sigma H D hback)).elim

/-- Directedness and AR incidence rule out irreducible arrows within a
translation orbit. -/
theorem not_irreducible_of_same_arOrbitLabel
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) {x y : Iota}
    (horbit : arOrbitLabel sigma H D x = arOrbitLabel sigma H D y) :
    ¬ HasIrreducibleMorphism (sigma.obj x) (sigma.obj y) := by
  intro hxy
  letI := directedLinearOrder sigma H
  let HO : DirectedHomOrder sigma :=
    DirectedHomOrder.of_acyclicNonzeroNonisomorphisms sigma H
  have hxylt : x < y := HO.lt_of_irreducible hxy
  have hxyReach :=
    arReach_of_arOrbitLabel_eq_of_irreducible sigma H D horbit hxy
  have hxyHeight : arHeight sigma D x < arHeight sigma D y :=
    arHeight_lt_of_arReach_of_ne sigma H D hxyReach hxylt.ne
  have hyNonprojective : ¬ Projective (sigma.obj y) := by
    intro hy
    exact hxylt.ne
      (reflTransGen_arStep_eq_of_projective_target sigma D hy hxyReach)
  let z : sigma.NonprojectiveLabel := ⟨y, hyNonprojective⟩
  have htaux : HasIrreducibleMorphism
      (sigma.obj (D.arTranslation sigma z).1) (sigma.obj x) :=
    (D.arTranslation_incidence sigma z x).1 hxy
  have htauOrbit : arOrbitLabel sigma H D (D.arTranslation sigma z).1 =
      arOrbitLabel sigma H D x :=
    (arOrbitLabel_translation sigma H D z).trans horbit.symm
  have htauxReach := arReach_of_arOrbitLabel_eq_of_irreducible
    sigma H D htauOrbit htaux
  have htauxHeight : arHeight sigma D (D.arTranslation sigma z).1 <
      arHeight sigma D x := arHeight_lt_of_arReach_of_ne sigma H D
    htauxReach (HO.lt_of_irreducible htaux).ne
  have hyHeight := arHeight_translation sigma H D z
  change arHeight sigma D y =
    arHeight sigma D (D.arTranslation sigma z).1 + 1 at hyHeight
  omega

/-- The inverse translation strictly increases the directed Hom order. -/
theorem arTranslationEquiv_symm_gt
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (z : sigma.NoninjectiveLabel) :
    letI := directedLinearOrder sigma H
    z.1 < ((D.arTranslationEquiv sigma).symm z).1 := by
  letI := directedLinearOrder sigma H
  let x : sigma.NonprojectiveLabel := (D.arTranslationEquiv sigma).symm z
  have hx := arTranslation_lt sigma H D x
  have htau : D.arTranslation sigma x = z := by
    exact (D.arTranslationEquiv sigma).apply_symm_apply z
  simpa only [htau] using hx

/-- Every label has an injective descendant in its finite translation chain. -/
theorem exists_injective_descendant
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (x : Iota) :
    ∃ i : Iota, Injective (sigma.obj i) ∧
      Relation.ReflTransGen (ARStep sigma D) x i := by
  letI := directedLinearOrder sigma H
  classical
  let descendants : Set Iota :=
    {i | Relation.ReflTransGen (ARStep sigma D) x i}
  have hx : x ∈ descendants := Relation.ReflTransGen.refl
  obtain ⟨i, hi, himax⟩ :=
    Set.Finite.exists_maximal (Set.toFinite descendants) ⟨x, hx⟩
  refine ⟨i, ?_, hi⟩
  by_contra hinj
  let z : sigma.NoninjectiveLabel := ⟨i, hinj⟩
  let y : sigma.NonprojectiveLabel := (D.arTranslationEquiv sigma).symm z
  have hiyStep : ARStep sigma D i y.1 := by
    refine ⟨y, ?_, rfl⟩
    have htau : D.arTranslation sigma y = z :=
      (D.arTranslationEquiv sigma).apply_symm_apply z
    exact congrArg Subtype.val htau |>.symm
  have hiy : i < y.1 := arTranslationEquiv_symm_gt sigma H D z
  have hy : y.1 ∈ descendants :=
    Relation.ReflTransGen.tail hi hiyStep
  exact (not_le_of_gt hiy) (himax hy hiy.le)

omit [Fintype Iota] in
/-- The injective descendant of a finite translation chain is unique. -/
theorem injective_descendant_unique
    (D : ARData sigma) {x i j : Iota}
    (hi : Injective (sigma.obj i))
    (hj : Injective (sigma.obj j))
    (hxi : Relation.ReflTransGen (ARStep sigma D) x i)
    (hxj : Relation.ReflTransGen (ARStep sigma D) x j) : i = j := by
  rcases reflTransGen_comparable_of_rightUnique
      (r := ARStep sigma D) (a := x) (b := i) (c := j)
      (fun hab hac ↦ arStep_rightUnique sigma D hab hac) hxi hxj with hij | hji
  · exact (reflTransGen_arStep_eq_of_injective_source sigma D hi hij).symm
  · exact reflTransGen_arStep_eq_of_injective_source sigma D hj hji

/-- Injective endpoints of finite translation chains. -/
def InjectiveLabel := {i : Iota // Injective (sigma.obj i)}

/-- The injective endpoint of the translation chain containing `x`. -/
def arOrbitInjectiveLabel
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (x : Iota) : InjectiveLabel sigma :=
  ⟨(exists_injective_descendant sigma H D x).choose,
    (exists_injective_descendant sigma H D x).choose_spec.1⟩

theorem reaches_arOrbitInjectiveLabel
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (x : Iota) :
    Relation.ReflTransGen (ARStep sigma D) x
      (arOrbitInjectiveLabel sigma H D x).1 :=
  (exists_injective_descendant sigma H D x).choose_spec.2

theorem arOrbitInjectiveLabel_eq_of_injective_descendant
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) {x i : Iota}
    (hi : Injective (sigma.obj i))
    (hxi : Relation.ReflTransGen (ARStep sigma D) x i) :
    arOrbitInjectiveLabel sigma H D x = ⟨i, hi⟩ := by
  apply Subtype.ext
  exact injective_descendant_unique sigma D
    (arOrbitInjectiveLabel sigma H D x).2 hi
    (reaches_arOrbitInjectiveLabel sigma H D x) hxi

theorem arOrbitInjectiveLabel_eq_self_of_injective
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) {i : Iota} (hi : Injective (sigma.obj i)) :
    arOrbitInjectiveLabel sigma H D i = ⟨i, hi⟩ :=
  arOrbitInjectiveLabel_eq_of_injective_descendant sigma H D hi
    Relation.ReflTransGen.refl

/-- Every injective endpoint occurs as the top of a translation orbit. -/
theorem arOrbitInjectiveLabel_surjective
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) :
    Function.Surjective (arOrbitInjectiveLabel sigma H D) := by
  intro i
  exact ⟨i.1, arOrbitInjectiveLabel_eq_self_of_injective sigma H D i.2⟩

theorem arOrbitInjectiveLabel_eq_of_reaches
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) {x y : Iota}
    (hxy : Relation.ReflTransGen (ARStep sigma D) x y) :
    arOrbitInjectiveLabel sigma H D x =
      arOrbitInjectiveLabel sigma H D y := by
  apply Subtype.ext
  exact injective_descendant_unique sigma D
    (arOrbitInjectiveLabel sigma H D x).2
    (arOrbitInjectiveLabel sigma H D y).2
    (reaches_arOrbitInjectiveLabel sigma H D x)
    (hxy.trans (reaches_arOrbitInjectiveLabel sigma H D y))

/-- Equality of projective orbit labels is equivalent to equality of the
injective endpoints of the same finite chains. -/
theorem arOrbitInjectiveLabel_eq_of_arOrbitLabel_eq
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) {x y : Iota}
    (horbit : arOrbitLabel sigma H D x = arOrbitLabel sigma H D y) :
    arOrbitInjectiveLabel sigma H D x =
      arOrbitInjectiveLabel sigma H D y := by
  rcases arReach_or_arReach_of_arOrbitLabel_eq sigma H D horbit with
      hxy | hyx
  · exact arOrbitInjectiveLabel_eq_of_reaches sigma H D hxy
  · exact (arOrbitInjectiveLabel_eq_of_reaches sigma H D hyx).symm

/-- Projective and injective endpoints label the same finite translation
orbits.  This is the intrinsic boundary relabeling used when coefficient
duality reverses the ordered Auslander--Reiten word. -/
def projectiveLabelEquivInjectiveLabel
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) :
    Equiv (ProjectiveLabel sigma) (InjectiveLabel sigma) where
  toFun p := arOrbitInjectiveLabel sigma H D p.1
  invFun i := arOrbitLabel sigma H D i.1
  left_inv p := by
    have hreach := reaches_arOrbitInjectiveLabel sigma H D p.1
    have horbit := arOrbitLabel_eq_of_reaches sigma H D hreach
    exact horbit.symm.trans
      (arOrbitLabel_eq_self_of_projective sigma H D p.2)
  right_inv i :=
    arOrbitInjectiveLabel_eq_of_injective_descendant
      sigma H D i.2 (arOrbitLabel_reaches sigma H D i.1)

@[simp]
theorem projectiveLabelEquivInjectiveLabel_apply
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (p : ProjectiveLabel sigma) :
    projectiveLabelEquivInjectiveLabel sigma H D p =
      arOrbitInjectiveLabel sigma H D p.1 :=
  rfl

@[simp]
theorem projectiveLabelEquivInjectiveLabel_symm_apply
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (i : InjectiveLabel sigma) :
    (projectiveLabelEquivInjectiveLabel sigma H D).symm i =
      arOrbitLabel sigma H D i.1 :=
  rfl

/-- The last height occurring in the translation orbit of `x`. -/
def arOrbitLength
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (x : Iota) : ℕ :=
  arHeight sigma D (arOrbitInjectiveLabel sigma H D x).1

theorem arOrbitLength_eq_of_arOrbitLabel_eq
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) {x y : Iota}
    (horbit : arOrbitLabel sigma H D x = arOrbitLabel sigma H D y) :
    arOrbitLength sigma H D x = arOrbitLength sigma H D y := by
  exact congrArg (arHeight sigma D ∘ Subtype.val)
    (arOrbitInjectiveLabel_eq_of_arOrbitLabel_eq sigma H D horbit)

theorem arHeight_le_arOrbitLength
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (x : Iota) :
    arHeight sigma D x ≤ arOrbitLength sigma H D x :=
  arHeight_le_of_arReach sigma D
    (reaches_arOrbitInjectiveLabel sigma H D x)

/-- Each height from zero through the injective endpoint occurs at exactly
one vertex of an orbit.  This is the intrinsic finite-chain formulation of
the first clause of the manuscript's two-orbit lemma. -/
theorem existsUnique_arOrbitLabel_eq_and_arHeight_eq
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (x : Iota) (n : ℕ)
    (hn : n ≤ arOrbitLength sigma H D x) :
    ∃! y : Iota,
      arOrbitLabel sigma H D y = arOrbitLabel sigma H D x ∧
        arHeight sigma D y = n := by
  let top : Iota := (arOrbitInjectiveLabel sigma H D x).1
  obtain ⟨y, hyReach, hyHeight⟩ :=
    exists_arReach_of_arHeight_eq sigma H D top n hn
  have hxtop : Relation.ReflTransGen (ARStep sigma D) x top :=
    reaches_arOrbitInjectiveLabel sigma H D x
  have hyOrbit : arOrbitLabel sigma H D y = arOrbitLabel sigma H D x :=
    (arOrbitLabel_eq_of_reaches sigma H D hyReach).trans
      (arOrbitLabel_eq_of_reaches sigma H D hxtop).symm
  refine ⟨y, ⟨hyOrbit, hyHeight⟩, ?_⟩
  intro z hz
  exact eq_of_arOrbitLabel_eq_of_arHeight_eq sigma H D
    (hz.1.trans hyOrbit.symm) (hz.2.trans hyHeight.symm)

/-- A vertex is injective exactly when its height is the final height of its
translation orbit. -/
theorem injective_iff_arHeight_eq_arOrbitLength
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (x : Iota) :
    Injective (sigma.obj x) ↔
      arHeight sigma D x = arOrbitLength sigma H D x := by
  constructor
  · intro hx
    have htop := arOrbitInjectiveLabel_eq_self_of_injective sigma H D hx
    exact congrArg (arHeight sigma D ∘ Subtype.val) htop.symm
  · intro hheight
    have horbit :
        arOrbitLabel sigma H D x =
          arOrbitLabel sigma H D
            (arOrbitInjectiveLabel sigma H D x).1 :=
      arOrbitLabel_eq_of_reaches sigma H D
        (reaches_arOrbitInjectiveLabel sigma H D x)
    have heq : x = (arOrbitInjectiveLabel sigma H D x).1 :=
      eq_of_arOrbitLabel_eq_of_arHeight_eq sigma H D horbit hheight
    rw [heq]
    exact (arOrbitInjectiveLabel sigma H D x).2

/-! ## Explicit directed-order variants

The intrinsic translation chains above do not depend on which linear
extension of the directed Hom relation is chosen.  The following small API
records exactly the order-dependent consequences for an arbitrary supplied
directed Hom order.  It is used when duality equips the opposite skeleton
with the literal reverse of a chosen source order.
-/

omit [Fintype Iota] in
/-- AR translation decreases every linear order compatible with nonzero
maps between distinct indecomposables. -/
theorem arTranslation_ltFor [LinearOrder Iota]
    (HO : DirectedHomOrder sigma)
    (D : ARData sigma) (z : sigma.NonprojectiveLabel) :
    (D.arTranslation sigma z).1 < z.1 := by
  let A := D.chosenRightAR sigma z
  let t : A.index :=
    Classical.choice (DirectedHomOrder.chosenRightAR_index_nonempty D z)
  let e : Iota := A.label t
  have hez : HasIrreducibleMorphism (sigma.obj e) (sigma.obj z.1) :=
    (A.summandIrreducibleCorrespondence e).1 ⟨t, rfl⟩
  have htaue : HasIrreducibleMorphism
      (sigma.obj (D.arTranslation sigma z).1) (sigma.obj e) :=
    (D.arTranslation_incidence sigma z e).1 hez
  exact (HO.lt_of_irreducible htaue).trans (HO.lt_of_irreducible hez)

omit [Fintype Iota] in
/-- Every AR step increases an arbitrary supplied directed Hom order. -/
theorem arStep_ltFor [LinearOrder Iota]
    (HO : DirectedHomOrder sigma)
    (D : ARData sigma) {x y : Iota} (hxy : ARStep sigma D x y) :
    x < y := by
  obtain ⟨z, rfl, rfl⟩ := hxy
  exact arTranslation_ltFor sigma HO D z

omit [Fintype Iota] in
/-- Translation reachability is monotone in an arbitrary supplied directed
Hom order. -/
theorem arReach_leFor [LinearOrder Iota]
    (HO : DirectedHomOrder sigma)
    (D : ARData sigma) {x y : Iota}
    (hxy : Relation.ReflTransGen (ARStep sigma D) x y) :
    x ≤ y := by
  induction hxy with
  | refl => exact le_rfl
  | tail _ hyz ih => exact ih.trans (arStep_ltFor sigma HO D hyz).le

/-- Immediately preceding occurrence in an AR orbit, relative to an
explicit ambient linear order. -/
def IsPreviousInOrbitFor [LinearOrder Iota]
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (p x : Iota) : Prop :=
  p < x ∧
    arOrbitLabel sigma H D p = arOrbitLabel sigma H D x ∧
    ∀ z : Iota, p < z → z < x →
      arOrbitLabel sigma H D z ≠ arOrbitLabel sigma H D x

/-- An explicit-order immediate predecessor is unique. -/
theorem isPreviousInOrbitFor_unique [LinearOrder Iota]
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) {p q x : Iota}
    (hp : IsPreviousInOrbitFor sigma H D p x)
    (hq : IsPreviousInOrbitFor sigma H D q x) : p = q := by
  rcases lt_trichotomy p q with hpq | hpq | hqp
  · exact False.elim (hp.2.2 q hpq hq.1 hq.2.1)
  · exact hpq
  · exact False.elim (hq.2.2 p hqp hp.1 hp.2.1)

/-- The AR translate is the explicit-order predecessor in its orbit. -/
theorem arTranslation_isPreviousInOrbitFor [LinearOrder Iota]
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (HO : DirectedHomOrder sigma)
    (D : ARData sigma) (z : sigma.NonprojectiveLabel) :
    IsPreviousInOrbitFor sigma H D (D.arTranslation sigma z).1 z.1 := by
  refine ⟨arTranslation_ltFor sigma HO D z,
    arOrbitLabel_translation sigma H D z, ?_⟩
  intro y htauy hyz hyOrbit
  have htauOrbit :
      arOrbitLabel sigma H D (D.arTranslation sigma z).1 =
        arOrbitLabel sigma H D y :=
    (arOrbitLabel_translation sigma H D z).trans hyOrbit.symm
  rcases arReach_or_arReach_of_arOrbitLabel_eq sigma H D htauOrbit with
      htauReach | hyReach
  · rcases Relation.ReflTransGen.cases_head htauReach with
      hEq | ⟨a, htaua, hay⟩
    · subst y
      exact (lt_irrefl _ htauy).elim
    · have ha : a = z.1 :=
        arStep_rightUnique sigma D htaua ⟨z, rfl, rfl⟩
      subst a
      exact (not_le_of_gt hyz) (arReach_leFor sigma HO D hay)
  · exact (not_le_of_gt htauy) (arReach_leFor sigma HO D hyReach)

/-- A vertex has an explicit-order predecessor in its orbit exactly when it
is nonprojective. -/
theorem exists_isPreviousInOrbitFor_iff_not_projective [LinearOrder Iota]
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (HO : DirectedHomOrder sigma)
    (D : ARData sigma) (x : Iota) :
    (∃ p : Iota, IsPreviousInOrbitFor sigma H D p x) ↔
      ¬ Projective (sigma.obj x) := by
  constructor
  · rintro ⟨p, hp⟩ hprojective
    rcases arReach_or_arReach_of_arOrbitLabel_eq sigma H D hp.2.1 with
        hpx | hxp
    · exact hp.1.ne
        (reflTransGen_arStep_eq_of_projective_target
          sigma D hprojective hpx)
    · exact (not_le_of_gt hp.1) (arReach_leFor sigma HO D hxp)
  · intro hprojective
    let z : sigma.NonprojectiveLabel := ⟨x, hprojective⟩
    exact ⟨(D.arTranslation sigma z).1,
      arTranslation_isPreviousInOrbitFor sigma H HO D z⟩

/-- The explicit-order predecessor at a nonprojective vertex is literally
its AR translate. -/
theorem isPreviousInOrbitFor_iff_eq_arTranslation [LinearOrder Iota]
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (HO : DirectedHomOrder sigma)
    (D : ARData sigma) (z : sigma.NonprojectiveLabel) (p : Iota) :
    IsPreviousInOrbitFor sigma H D p z.1 ↔
      p = (D.arTranslation sigma z).1 := by
  constructor
  · intro hp
    exact isPreviousInOrbitFor_unique sigma H D hp
      (arTranslation_isPreviousInOrbitFor sigma H HO D z)
  · rintro rfl
    exact arTranslation_isPreviousInOrbitFor sigma H HO D z

end QuotientSubmoduleEquidistribution.RepresentationDirected.DirectedAROrbit
