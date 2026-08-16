import QuotientSubmoduleEquidistribution.RepresentationDirected.DirectedAROrbits

/-!
# Interlacing of two directed Auslander--Reiten orbits

This file proves the manuscript's fixed-offset two-orbit lemma.  A single
irreducible arrow fixes an integral offset between two finite translation
chains.  AR incidence propagates that arrow along both chains, including all
projective and injective boundary cases.  The resulting seed-adjusted height
totally interlaces the two orbits and classifies every irreducible arrow in
either orientation.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.RepresentationDirected.DirectedAROrbit.TwoOrbits

universe uR uIota

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {Iota : Type uIota} [Fintype Iota]
  (sigma : IndecomposableSkeleton.{uR, uIota, uR} R Iota)

abbrev ARData := sigma.FiniteARTranslationData

/-- The partial successor in a finite AR translation chain. -/
def arSuccessor (D : ARData sigma) (x : sigma.NoninjectiveLabel) :
    sigma.NonprojectiveLabel :=
  (D.arTranslationEquiv sigma).symm x

theorem arTranslation_arSuccessor
    (D : ARData sigma) (x : sigma.NoninjectiveLabel) :
    D.arTranslation sigma (arSuccessor sigma D x) = x :=
  (D.arTranslationEquiv sigma).apply_symm_apply x

theorem arSuccessor_height
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (x : sigma.NoninjectiveLabel) :
    arHeight sigma D (arSuccessor sigma D x).1 =
      arHeight sigma D x.1 + 1 := by
  have h := arHeight_translation sigma H D (arSuccessor sigma D x)
  rw [arTranslation_arSuccessor sigma D x] at h
  exact h

theorem arSuccessor_orbitLabel
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (x : sigma.NoninjectiveLabel) :
    arOrbitLabel sigma H D (arSuccessor sigma D x).1 =
      arOrbitLabel sigma H D x.1 := by
  have h := arOrbitLabel_translation sigma H D (arSuccessor sigma D x)
  rw [arTranslation_arSuccessor sigma D x] at h
  exact h.symm

/-- Every height below a vertex occurs exactly once in its finite translation
chain.  Existence is the useful half; uniqueness follows from the production
root/height coordinate theorem. -/
theorem exists_arOrbitLabel_eq_arHeight_eq_of_le
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) (y : Iota) (h : ℕ)
    (hle : h ≤ arHeight sigma D y) :
    ∃ x : Iota, arOrbitLabel sigma H D x = arOrbitLabel sigma H D y ∧
      arHeight sigma D x = h := by
  obtain ⟨x, hxy, hxHeight⟩ :=
    exists_arReach_of_arHeight_eq sigma H D y h hle
  exact ⟨x, arOrbitLabel_eq_of_reaches sigma H D hxy, hxHeight⟩

/-- The inverse form of AR incidence: an arrow out of a noninjective vertex
rotates to an arrow into its translation successor. -/
theorem arSuccessor_incidence
    (D : ARData sigma) (x : sigma.NoninjectiveLabel) (y : Iota) :
    HasIrreducibleMorphism (sigma.obj x.1) (sigma.obj y) ↔
      HasIrreducibleMorphism (sigma.obj y)
        (sigma.obj (arSuccessor sigma D x).1) := by
  have h := (D.arTranslation_incidence sigma
    (arSuccessor sigma D x) y).symm
  rw [arTranslation_arSuccessor sigma D x] at h
  exact h

omit [Fintype Iota] in
/-- One arrow propagates two places toward the projective ends when both
targets admit translation. -/
theorem irreducible_backward_pair
    (D : ARData sigma) (x y : sigma.NonprojectiveLabel)
    (hxy : HasIrreducibleMorphism (sigma.obj x.1) (sigma.obj y.1)) :
    HasIrreducibleMorphism
        (sigma.obj (D.arTranslation sigma y).1) (sigma.obj x.1) ∧
      HasIrreducibleMorphism
        (sigma.obj (D.arTranslation sigma x).1)
        (sigma.obj (D.arTranslation sigma y).1) := by
  have hyx : HasIrreducibleMorphism
      (sigma.obj (D.arTranslation sigma y).1) (sigma.obj x.1) :=
    (D.arTranslation_incidence sigma y x.1).1 hxy
  exact ⟨hyx, (D.arTranslation_incidence sigma x
    (D.arTranslation sigma y).1).1 hyx⟩

/-- One arrow propagates two places toward the injective ends when both
sources admit inverse translation. -/
theorem irreducible_forward_pair
    (D : ARData sigma) (x y : sigma.NoninjectiveLabel)
    (hxy : HasIrreducibleMorphism (sigma.obj x.1) (sigma.obj y.1)) :
    HasIrreducibleMorphism (sigma.obj y.1)
        (sigma.obj (arSuccessor sigma D x).1) ∧
      HasIrreducibleMorphism (sigma.obj (arSuccessor sigma D x).1)
        (sigma.obj (arSuccessor sigma D y).1) := by
  have hysx : HasIrreducibleMorphism (sigma.obj y.1)
      (sigma.obj (arSuccessor sigma D x).1) :=
    (arSuccessor_incidence sigma D x y.1).1 hxy
  exact ⟨hysx, (arSuccessor_incidence sigma D y
    (arSuccessor sigma D x).1).1 hysx⟩

omit [Fintype Iota] in
theorem not_injective_of_arReach_of_ne
    (D : ARData sigma) {x y : Iota}
    (hxy : Relation.ReflTransGen (ARStep sigma D) x y) (hne : x ≠ y) :
    ¬ Injective (sigma.obj x) := by
  intro hx
  exact hne
    (reflTransGen_arStep_eq_of_injective_source sigma D hx hxy).symm

omit [Fintype Iota] in
theorem not_projective_of_arReach_of_ne
    (D : ARData sigma) {x y : Iota}
    (hxy : Relation.ReflTransGen (ARStep sigma D) x y) (hne : x ≠ y) :
    ¬ Projective (sigma.obj y) := by
  intro hy
  exact hne (reflTransGen_arStep_eq_of_projective_target sigma D hy hxy)

theorem arReach_to_injective_of_arOrbitLabel_eq
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) {x i : Iota} (hi : Injective (sigma.obj i))
    (horbit : arOrbitLabel sigma H D x = arOrbitLabel sigma H D i) :
    Relation.ReflTransGen (ARStep sigma D) x i := by
  have hrootx := arOrbitLabel_reaches sigma H D x
  have hrooti : Relation.ReflTransGen (ARStep sigma D)
      (arOrbitLabel sigma H D x).1 i := by
    simpa only [horbit] using arOrbitLabel_reaches sigma H D i
  rcases reflTransGen_comparable_of_rightUnique
      (r := ARStep sigma D)
      (fun hab hac ↦ arStep_rightUnique sigma D hab hac)
      hrootx hrooti with hxi | hix
  · exact hxi
  · have hxi :=
      reflTransGen_arStep_eq_of_injective_source sigma D hi hix
    subst x
    exact Relation.ReflTransGen.refl

/-- Diagonal propagation toward the injective ends: moving both endpoints
forward by the same number of translation steps preserves an arrow. -/
theorem irreducible_diagonal_forward
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) {x y x' y' : Iota}
    (hxy : HasIrreducibleMorphism (sigma.obj x) (sigma.obj y))
    (hox : arOrbitLabel sigma H D x = arOrbitLabel sigma H D x')
    (hoy : arOrbitLabel sigma H D y = arOrbitLabel sigma H D y')
    (n : ℕ)
    (hxx' : arHeight sigma D x' = arHeight sigma D x + n)
    (hyy' : arHeight sigma D y' = arHeight sigma D y + n) :
    HasIrreducibleMorphism (sigma.obj x') (sigma.obj y') := by
  induction n generalizing x y with
  | zero =>
      have hx : x = x' := eq_of_arOrbitLabel_eq_of_arHeight_eq
        sigma H D hox hxx'.symm
      have hy : y = y' := eq_of_arOrbitLabel_eq_of_arHeight_eq
        sigma H D hoy hyy'.symm
      simpa only [hx, hy] using hxy
  | succ n ih =>
      have hxx'lt : arHeight sigma D x < arHeight sigma D x' := by
        omega
      have hyy'lt : arHeight sigma D y < arHeight sigma D y' := by
        omega
      have hreachX : Relation.ReflTransGen (ARStep sigma D) x x' :=
        arReach_of_arOrbitLabel_eq_of_arHeight_le sigma H D hox hxx'lt.le
      have hreachY : Relation.ReflTransGen (ARStep sigma D) y y' :=
        arReach_of_arOrbitLabel_eq_of_arHeight_le sigma H D hoy hyy'lt.le
      let xn : sigma.NoninjectiveLabel :=
        ⟨x, not_injective_of_arReach_of_ne sigma D hreachX
          (fun h ↦ by subst x'; omega)⟩
      let yn : sigma.NoninjectiveLabel :=
        ⟨y, not_injective_of_arReach_of_ne sigma D hreachY
          (fun h ↦ by subst y'; omega)⟩
      have hnext : HasIrreducibleMorphism
          (sigma.obj (arSuccessor sigma D xn).1)
          (sigma.obj (arSuccessor sigma D yn).1) :=
        (irreducible_forward_pair sigma D xn yn hxy).2
      apply ih hnext
      · exact (arSuccessor_orbitLabel sigma H D xn).trans hox
      · exact (arSuccessor_orbitLabel sigma H D yn).trans hoy
      · rw [arSuccessor_height sigma H D xn]
        change arHeight sigma D x' = arHeight sigma D x + 1 + n
        omega
      · rw [arSuccessor_height sigma H D yn]
        change arHeight sigma D y' = arHeight sigma D y + 1 + n
        omega

/-- Diagonal propagation toward the projective ends: moving both endpoints
back by the same number of translation steps preserves an arrow. -/
theorem irreducible_diagonal_backward
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) {x y x' y' : Iota}
    (hxy : HasIrreducibleMorphism (sigma.obj x) (sigma.obj y))
    (hox : arOrbitLabel sigma H D x = arOrbitLabel sigma H D x')
    (hoy : arOrbitLabel sigma H D y = arOrbitLabel sigma H D y')
    (n : ℕ)
    (hxx' : arHeight sigma D x = arHeight sigma D x' + n)
    (hyy' : arHeight sigma D y = arHeight sigma D y' + n) :
    HasIrreducibleMorphism (sigma.obj x') (sigma.obj y') := by
  induction n generalizing x y with
  | zero =>
      have hx : x = x' := eq_of_arOrbitLabel_eq_of_arHeight_eq
        sigma H D hox hxx'
      have hy : y = y' := eq_of_arOrbitLabel_eq_of_arHeight_eq
        sigma H D hoy hyy'
      simpa only [hx, hy] using hxy
  | succ n ih =>
      have hxpos : 0 < arHeight sigma D x := by omega
      have hypos : 0 < arHeight sigma D y := by omega
      let xp : sigma.NonprojectiveLabel :=
        ⟨x, (arHeight_pos_iff_nonprojective sigma H D x).mp hxpos⟩
      let yp : sigma.NonprojectiveLabel :=
        ⟨y, (arHeight_pos_iff_nonprojective sigma H D y).mp hypos⟩
      have hprev : HasIrreducibleMorphism
          (sigma.obj (D.arTranslation sigma xp).1)
          (sigma.obj (D.arTranslation sigma yp).1) :=
        (irreducible_backward_pair sigma D xp yp hxy).2
      apply ih hprev
      · exact (arOrbitLabel_translation sigma H D xp).trans hox
      · exact (arOrbitLabel_translation sigma H D yp).trans hoy
      · have hxHeight := arHeight_translation sigma H D xp
        change arHeight sigma D x =
          arHeight sigma D (D.arTranslation sigma xp).1 + 1 at hxHeight
        omega
      · have hyHeight := arHeight_translation sigma H D yp
        change arHeight sigma D y =
          arHeight sigma D (D.arTranslation sigma yp).1 + 1 at hyHeight
        omega

/-! ## Terminal left rotation

The manuscript proof of the two-orbit lemma rotates an irreducible arrow to
the left until its target is projective.  The two alternatives below record
the parity of the number of rotations without subtraction: an even number
keeps the orientation of the two translation orbits, while an odd number
reverses it and shifts the height equation by one.
-/

/-- Every irreducible arrow has a terminal left rotation whose target is
projective. -/
theorem exists_terminal_left_rotation
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) {x y : Iota}
    (hxy : HasIrreducibleMorphism (sigma.obj x) (sigma.obj y)) :
    ∃ a p : Iota, Projective (sigma.obj p) ∧
      HasIrreducibleMorphism (sigma.obj a) (sigma.obj p) ∧
      ((arOrbitLabel sigma H D a = arOrbitLabel sigma H D x ∧
          arOrbitLabel sigma H D p = arOrbitLabel sigma H D y ∧
          arHeight sigma D x + arHeight sigma D p =
            arHeight sigma D y + arHeight sigma D a) ∨
        (arOrbitLabel sigma H D a = arOrbitLabel sigma H D y ∧
          arOrbitLabel sigma H D p = arOrbitLabel sigma H D x ∧
          arHeight sigma D x + arHeight sigma D a + 1 =
            arHeight sigma D y + arHeight sigma D p)) := by
  induction hmeasure : arHeight sigma D x + arHeight sigma D y using
      Nat.strong_induction_on generalizing x y with
  | h n ih =>
      subst n
      by_cases hyProjective : Projective (sigma.obj y)
      · refine ⟨x, y, hyProjective, hxy, Or.inl ⟨rfl, rfl, ?_⟩⟩
        have hyHeight := arHeight_eq_zero_of_projective sigma D hyProjective
        omega
      · let yp : sigma.NonprojectiveLabel := ⟨y, hyProjective⟩
        have hleft : HasIrreducibleMorphism
            (sigma.obj (D.arTranslation sigma yp).1) (sigma.obj x) :=
          (D.arTranslation_incidence sigma yp x).1 hxy
        have hyHeight := arHeight_translation sigma H D yp
        change arHeight sigma D y =
          arHeight sigma D (D.arTranslation sigma yp).1 + 1 at hyHeight
        have hmeasure' :
            arHeight sigma D (D.arTranslation sigma yp).1 +
                arHeight sigma D x <
              arHeight sigma D x + arHeight sigma D y := by
          omega
        obtain ⟨a, p, hp, hap, hterminal⟩ :=
          ih _ hmeasure' hleft rfl
        refine ⟨a, p, hp, hap, ?_⟩
        rcases hterminal with hsame | hreverse
        · right
          refine ⟨hsame.1.trans (arOrbitLabel_translation
            sigma H D yp), hsame.2.1, ?_⟩
          omega
        · left
          refine ⟨hreverse.1, hreverse.2.1.trans
            (arOrbitLabel_translation sigma H D yp), ?_⟩
          omega

/-- Two terminal arrows cannot point in opposite directions between the same
two translation orbits. -/
theorem terminal_arrows_not_opposite
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) {a p b q : Iota}
    (hp : Projective (sigma.obj p)) (hq : Projective (sigma.obj q))
    (hap : HasIrreducibleMorphism (sigma.obj a) (sigma.obj p))
    (hbq : HasIrreducibleMorphism (sigma.obj b) (sigma.obj q))
    (haq : arOrbitLabel sigma H D a = arOrbitLabel sigma H D q)
    (hpb : arOrbitLabel sigma H D p = arOrbitLabel sigma H D b) : False := by
  letI := directedLinearOrder sigma H
  let HO : DirectedHomOrder sigma :=
    DirectedHomOrder.of_acyclicNonzeroNonisomorphisms sigma H
  have hqHeight := arHeight_eq_zero_of_projective sigma D hq
  have hpHeight := arHeight_eq_zero_of_projective sigma D hp
  have hqa : Relation.ReflTransGen (ARStep sigma D) q a :=
    arReach_of_arOrbitLabel_eq_of_arHeight_le sigma H D haq.symm (by omega)
  have hpbReach : Relation.ReflTransGen (ARStep sigma D) p b :=
    arReach_of_arOrbitLabel_eq_of_arHeight_le sigma H D hpb (by omega)
  have hqp : q < p :=
    ((arReach_le sigma H D hqa).trans_lt
      (HO.lt_of_irreducible hap))
  have hpq : p < q :=
    ((arReach_le sigma H D hpbReach).trans_lt
      (HO.lt_of_irreducible hbq))
  exact (lt_asymm hqp hpq).elim

/-- Terminal arrows with the same oriented pair of translation orbits have
the same projective target and the same source. -/
theorem terminal_arrows_eq_of_same_orbits
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) {a p b q : Iota}
    (hp : Projective (sigma.obj p)) (hq : Projective (sigma.obj q))
    (hap : HasIrreducibleMorphism (sigma.obj a) (sigma.obj p))
    (hbq : HasIrreducibleMorphism (sigma.obj b) (sigma.obj q))
    (hab : arOrbitLabel sigma H D a = arOrbitLabel sigma H D b)
    (hpqOrbit : arOrbitLabel sigma H D p = arOrbitLabel sigma H D q) :
    a = b ∧ p = q := by
  have hpq : p = q := by
    have hpSelf := arOrbitLabel_eq_self_of_projective sigma H D hp
    have hqSelf := arOrbitLabel_eq_self_of_projective sigma H D hq
    exact congrArg Subtype.val (hpSelf.symm.trans (hpqOrbit.trans hqSelf))
  subst q
  refine ⟨?_, rfl⟩
  apply eq_of_arOrbitLabel_eq_of_arHeight_eq sigma H D hab
  by_contra hheight
  letI := directedLinearOrder sigma H
  let HO : DirectedHomOrder sigma :=
    DirectedHomOrder.of_acyclicNonzeroNonisomorphisms sigma H
  rcases lt_or_gt_of_ne hheight with habHeight | hbaHeight
  · have habNe : a ≠ b := fun habEq ↦ by subst b; omega
    have habReach := arReach_of_arOrbitLabel_eq_of_arHeight_le
      sigma H D hab habHeight.le
    let an : sigma.NoninjectiveLabel :=
      ⟨a, not_injective_of_arReach_of_ne sigma D habReach habNe⟩
    have hpaSucc : HasIrreducibleMorphism (sigma.obj p)
        (sigma.obj (arSuccessor sigma D an).1) :=
      (arSuccessor_incidence sigma D an p).1 hap
    have hsuccOrbit : arOrbitLabel sigma H D
        (arSuccessor sigma D an).1 = arOrbitLabel sigma H D b :=
      (arSuccessor_orbitLabel sigma H D an).trans hab
    have hsuccHeight := arSuccessor_height sigma H D an
    change arHeight sigma D (arSuccessor sigma D an).1 =
      arHeight sigma D a + 1 at hsuccHeight
    have hsuccBReach := arReach_of_arOrbitLabel_eq_of_arHeight_le
      sigma H D hsuccOrbit (by omega)
    have hpb : p < b := (HO.lt_of_irreducible hpaSucc).trans_le
      (arReach_le sigma H D hsuccBReach)
    exact (lt_asymm hpb (HO.lt_of_irreducible hbq)).elim
  · have hbaNe : b ≠ a := fun hbaEq ↦ by subst b; omega
    have hbaReach := arReach_of_arOrbitLabel_eq_of_arHeight_le
      sigma H D hab.symm hbaHeight.le
    let bn : sigma.NoninjectiveLabel :=
      ⟨b, not_injective_of_arReach_of_ne sigma D hbaReach hbaNe⟩
    have hpbSucc : HasIrreducibleMorphism (sigma.obj p)
        (sigma.obj (arSuccessor sigma D bn).1) :=
      (arSuccessor_incidence sigma D bn p).1 hbq
    have hsuccOrbit : arOrbitLabel sigma H D
        (arSuccessor sigma D bn).1 = arOrbitLabel sigma H D a :=
      (arSuccessor_orbitLabel sigma H D bn).trans hab.symm
    have hsuccHeight := arSuccessor_height sigma H D bn
    change arHeight sigma D (arSuccessor sigma D bn).1 =
      arHeight sigma D b + 1 at hsuccHeight
    have hsuccAReach := arReach_of_arOrbitLabel_eq_of_arHeight_le
      sigma H D hsuccOrbit (by omega)
    have hpa : p < a := (HO.lt_of_irreducible hpbSucc).trans_le
      (arReach_le sigma H D hsuccAReach)
    exact (lt_asymm hpa (HO.lt_of_irreducible hap)).elim

/-- A seed arrow fixes the cross-orbit height order on its forward side.
The inequality is the subtraction-free form of
`height x ≤ height y - (height v - height u)`. -/
theorem lt_of_seed_irreducible_of_cross_height_le
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) {u v x y : Iota}
    (huv : HasIrreducibleMorphism (sigma.obj u) (sigma.obj v))
    (hxu : arOrbitLabel sigma H D x = arOrbitLabel sigma H D u)
    (hyv : arOrbitLabel sigma H D y = arOrbitLabel sigma H D v)
    (hcross : arHeight sigma D x + arHeight sigma D v ≤
      arHeight sigma D y + arHeight sigma D u) :
    letI := directedLinearOrder sigma H
    x < y := by
  letI := directedLinearOrder sigma H
  let HO : DirectedHomOrder sigma :=
    DirectedHomOrder.of_acyclicNonzeroNonisomorphisms sigma H
  let t : ℕ := arHeight sigma D y + arHeight sigma D u -
    arHeight sigma D v
  have hvle : arHeight sigma D v ≤
      arHeight sigma D y + arHeight sigma D u := by omega
  have htEq : t + arHeight sigma D v =
      arHeight sigma D y + arHeight sigma D u := by
    exact Nat.sub_add_cancel hvle
  have hxt : arHeight sigma D x ≤ t := by omega
  obtain ⟨ur, hurInjective, huur⟩ :=
    exists_injective_descendant sigma H D u
  have huUrOrbit : arOrbitLabel sigma H D u = arOrbitLabel sigma H D ur :=
    arOrbitLabel_eq_of_reaches sigma H D huur
  have huUrHeight : arHeight sigma D u ≤ arHeight sigma D ur :=
    arHeight_le_of_arReach sigma D huur
  by_cases htur : t ≤ arHeight sigma D ur
  · obtain ⟨ut, hutUrOrbit, hutHeight⟩ :=
      exists_arOrbitLabel_eq_arHeight_eq_of_le sigma H D ur t htur
    have huUtOrbit : arOrbitLabel sigma H D u =
        arOrbitLabel sigma H D ut := huUrOrbit.trans hutUrOrbit.symm
    have hvYOrbit : arOrbitLabel sigma H D v =
        arOrbitLabel sigma H D y := hyv.symm
    have hutY : HasIrreducibleMorphism (sigma.obj ut) (sigma.obj y) := by
      by_cases hut : arHeight sigma D u ≤ t
      · let n := t - arHeight sigma D u
        apply irreducible_diagonal_forward sigma H D huv huUtOrbit hvYOrbit n
        · omega
        · omega
      · let n := arHeight sigma D u - t
        apply irreducible_diagonal_backward sigma H D huv huUtOrbit hvYOrbit n
        · omega
        · omega
    have hxUtOrbit : arOrbitLabel sigma H D x =
        arOrbitLabel sigma H D ut := hxu.trans huUtOrbit
    have hxUtHeight : arHeight sigma D x ≤ arHeight sigma D ut := by
      rw [hutHeight]
      exact hxt
    have hxUtReach := arReach_of_arOrbitLabel_eq_of_arHeight_le
      sigma H D hxUtOrbit hxUtHeight
    exact (arReach_le sigma H D hxUtReach).trans_lt
      (HO.lt_of_irreducible hutY)
  · have hurt : arHeight sigma D ur < t := by omega
    let n := arHeight sigma D ur - arHeight sigma D u
    let l := arHeight sigma D v + n
    have hlY : l ≤ arHeight sigma D y := by omega
    obtain ⟨vl, hvlYOrbit, hvlHeight⟩ :=
      exists_arOrbitLabel_eq_arHeight_eq_of_le sigma H D y l hlY
    have hvVlOrbit : arOrbitLabel sigma H D v =
        arOrbitLabel sigma H D vl := hyv.symm.trans hvlYOrbit.symm
    have hurVl : HasIrreducibleMorphism (sigma.obj ur) (sigma.obj vl) := by
      apply irreducible_diagonal_forward sigma H D huv huUrOrbit hvVlOrbit n
      · omega
      · omega
    have hxUrReach := arReach_to_injective_of_arOrbitLabel_eq sigma H D
      hurInjective (hxu.trans huUrOrbit)
    have hvlYReach := arReach_of_arOrbitLabel_eq_of_arHeight_le
      sigma H D hvlYOrbit (by omega)
    exact ((arReach_le sigma H D hxUrReach).trans_lt
      (HO.lt_of_irreducible hurVl)).trans_le
      (arReach_le sigma H D hvlYReach)

/-- The complementary arithmetic inequality gives the opposite cross-orbit
order.  At the injective boundary of the first seed orbit, rotate backward
at the second seed vertex instead. -/
theorem lt_of_seed_irreducible_of_cross_height_gt
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) {u v x y : Iota}
    (huv : HasIrreducibleMorphism (sigma.obj u) (sigma.obj v))
    (hxu : arOrbitLabel sigma H D x = arOrbitLabel sigma H D u)
    (hyv : arOrbitLabel sigma H D y = arOrbitLabel sigma H D v)
    (hcross : arHeight sigma D y + arHeight sigma D u <
      arHeight sigma D x + arHeight sigma D v) :
    letI := directedLinearOrder sigma H
    y < x := by
  letI := directedLinearOrder sigma H
  by_cases huInjective : Injective (sigma.obj u)
  · have hxuReach := arReach_to_injective_of_arOrbitLabel_eq sigma H D
      huInjective hxu
    have hxuHeight : arHeight sigma D x ≤ arHeight sigma D u :=
      arHeight_le_of_arReach sigma D hxuReach
    have hvpos : 0 < arHeight sigma D v := by omega
    let vp : sigma.NonprojectiveLabel :=
      ⟨v, (arHeight_pos_iff_nonprojective sigma H D v).mp hvpos⟩
    have hback : HasIrreducibleMorphism
        (sigma.obj (D.arTranslation sigma vp).1) (sigma.obj u) :=
      (D.arTranslation_incidence sigma vp u).1 huv
    have hyTauV : arOrbitLabel sigma H D y =
        arOrbitLabel sigma H D (D.arTranslation sigma vp).1 :=
      hyv.trans (arOrbitLabel_translation sigma H D vp).symm
    have hvHeight := arHeight_translation sigma H D vp
    change arHeight sigma D v =
      arHeight sigma D (D.arTranslation sigma vp).1 + 1 at hvHeight
    exact lt_of_seed_irreducible_of_cross_height_le sigma H D
      hback hyTauV hxu (by omega)
  · let un : sigma.NoninjectiveLabel := ⟨u, huInjective⟩
    have hforward : HasIrreducibleMorphism (sigma.obj v)
        (sigma.obj (arSuccessor sigma D un).1) :=
      (arSuccessor_incidence sigma D un v).1 huv
    have hxSuccU : arOrbitLabel sigma H D x =
        arOrbitLabel sigma H D (arSuccessor sigma D un).1 :=
      hxu.trans (arSuccessor_orbitLabel sigma H D un).symm
    have huHeight := arSuccessor_height sigma H D un
    change arHeight sigma D (arSuccessor sigma D un).1 =
      arHeight sigma D u + 1 at huHeight
    exact lt_of_seed_irreducible_of_cross_height_le sigma H D
      hforward hyv hxSuccU (by omega)

/-- The two seed orbits are totally interlaced by the seed-adjusted height. -/
theorem two_arOrbits_cross_comparable
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) {u v x y : Iota}
    (huv : HasIrreducibleMorphism (sigma.obj u) (sigma.obj v))
    (hxu : arOrbitLabel sigma H D x = arOrbitLabel sigma H D u)
    (hyv : arOrbitLabel sigma H D y = arOrbitLabel sigma H D v) :
    letI := directedLinearOrder sigma H
    x < y ∨ y < x := by
  letI := directedLinearOrder sigma H
  by_cases hcross : arHeight sigma D x + arHeight sigma D v ≤
      arHeight sigma D y + arHeight sigma D u
  · exact Or.inl (lt_of_seed_irreducible_of_cross_height_le
      sigma H D huv hxu hyv hcross)
  · exact Or.inr (lt_of_seed_irreducible_of_cross_height_gt
      sigma H D huv hxu hyv (by omega))

/-- Exact interlacing criterion for the chosen directed order: a vertex on
the seed's source orbit precedes a vertex on its target orbit precisely when
its seed-adjusted height is weakly smaller. -/
theorem lt_iff_seed_cross_height_le
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) {u v x y : Iota}
    (huv : HasIrreducibleMorphism (sigma.obj u) (sigma.obj v))
    (hxu : arOrbitLabel sigma H D x = arOrbitLabel sigma H D u)
    (hyv : arOrbitLabel sigma H D y = arOrbitLabel sigma H D v) :
    letI := directedLinearOrder sigma H
    x < y ↔ arHeight sigma D x + arHeight sigma D v ≤
      arHeight sigma D y + arHeight sigma D u := by
  letI := directedLinearOrder sigma H
  constructor
  · intro hxy
    by_contra hnot
    have hyx := lt_of_seed_irreducible_of_cross_height_gt
      sigma H D huv hxu hyv (by omega)
    exact lt_asymm hxy hyx
  · exact lt_of_seed_irreducible_of_cross_height_le
      sigma H D huv hxu hyv

/-- The complementary strict height inequality is exactly the reverse
cross-orbit order. -/
theorem reverse_lt_iff_seed_cross_height_gt
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) {u v x y : Iota}
    (huv : HasIrreducibleMorphism (sigma.obj u) (sigma.obj v))
    (hxu : arOrbitLabel sigma H D x = arOrbitLabel sigma H D u)
    (hyv : arOrbitLabel sigma H D y = arOrbitLabel sigma H D v) :
    letI := directedLinearOrder sigma H
    y < x ↔ arHeight sigma D y + arHeight sigma D u <
      arHeight sigma D x + arHeight sigma D v := by
  letI := directedLinearOrder sigma H
  constructor
  · intro hyx
    by_contra hnot
    have hxy := lt_of_seed_irreducible_of_cross_height_le
      sigma H D huv hxu hyv (by omega)
    exact lt_asymm hyx hxy
  · exact lt_of_seed_irreducible_of_cross_height_gt
      sigma H D huv hxu hyv

/-- Once an arrow `u ⟶ v` fixes the relative offset of two translation
orbits, the arrows in the same orientation are exactly the pairs at that
offset.  The equality is the subtraction-free form of
`height x - height u = height y - height v`. -/
theorem irreducible_same_orientation_iff_height_offset
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) {u v x y : Iota}
    (huv : HasIrreducibleMorphism (sigma.obj u) (sigma.obj v))
    (hxu : arOrbitLabel sigma H D x = arOrbitLabel sigma H D u)
    (hyv : arOrbitLabel sigma H D y = arOrbitLabel sigma H D v) :
    HasIrreducibleMorphism (sigma.obj x) (sigma.obj y) ↔
      arHeight sigma D x + arHeight sigma D v =
        arHeight sigma D y + arHeight sigma D u := by
  constructor
  · intro hxy
    obtain ⟨a, p, hp, hap, hterminalUV⟩ :=
      exists_terminal_left_rotation sigma H D huv
    obtain ⟨b, q, hq, hbq, hterminalXY⟩ :=
      exists_terminal_left_rotation sigma H D hxy
    rcases hterminalUV with huvSame | huvReverse <;>
      rcases hterminalXY with hxySame | hxyReverse
    · obtain ⟨hab, hpq⟩ := terminal_arrows_eq_of_same_orbits
        sigma H D hp hq hap hbq
        (huvSame.1.trans (hxu.symm.trans hxySame.1.symm))
        (huvSame.2.1.trans (hyv.symm.trans hxySame.2.1.symm))
      subst b
      subst q
      omega
    · exact (terminal_arrows_not_opposite sigma H D hp hq hap hbq
        (huvSame.1.trans (hxu.symm.trans hxyReverse.2.1.symm))
        (huvSame.2.1.trans (hyv.symm.trans hxyReverse.1.symm))).elim
    · exact (terminal_arrows_not_opposite sigma H D hp hq hap hbq
        (huvReverse.1.trans (hyv.symm.trans hxySame.2.1.symm))
        (huvReverse.2.1.trans (hxu.symm.trans hxySame.1.symm))).elim
    · obtain ⟨hab, hpq⟩ := terminal_arrows_eq_of_same_orbits
        sigma H D hp hq hap hbq
        (huvReverse.1.trans (hyv.symm.trans hxyReverse.1.symm))
        (huvReverse.2.1.trans (hxu.symm.trans hxyReverse.2.1.symm))
      subst b
      subst q
      omega
  · intro hoffset
    by_cases hux : arHeight sigma D u ≤ arHeight sigma D x
    · let n := arHeight sigma D x - arHeight sigma D u
      apply irreducible_diagonal_forward sigma H D huv hxu.symm hyv.symm n
      · dsimp [n]
        omega
      · dsimp [n]
        omega
    · let n := arHeight sigma D u - arHeight sigma D x
      apply irreducible_diagonal_backward sigma H D huv hxu.symm hyv.symm n
      · dsimp [n]
        omega
      · dsimp [n]
        omega

/-- The arrows in the reverse orientation occupy the adjacent offset.  This
is the subtraction-free form of
`height x - height u = height y - height v + 1`. -/
theorem irreducible_reverse_orientation_iff_height_offset
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) {u v x y : Iota}
    (huv : HasIrreducibleMorphism (sigma.obj u) (sigma.obj v))
    (hxu : arOrbitLabel sigma H D x = arOrbitLabel sigma H D u)
    (hyv : arOrbitLabel sigma H D y = arOrbitLabel sigma H D v) :
    HasIrreducibleMorphism (sigma.obj y) (sigma.obj x) ↔
      arHeight sigma D y + arHeight sigma D u + 1 =
        arHeight sigma D x + arHeight sigma D v := by
  by_cases hxProjective : Projective (sigma.obj x)
  · have hxHeight : arHeight sigma D x = 0 :=
      (arHeight_eq_zero_iff_projective sigma H D x).2 hxProjective
    by_cases hyInjective : Injective (sigma.obj y)
    · have hvyReach : Relation.ReflTransGen (ARStep sigma D) v y :=
        arReach_to_injective_of_arOrbitLabel_eq sigma H D
          hyInjective hyv.symm
      have hvyHeight : arHeight sigma D v ≤ arHeight sigma D y :=
        arHeight_le_of_arReach sigma D hvyReach
      constructor
      · intro hyx
        letI := directedLinearOrder sigma H
        let HO : DirectedHomOrder sigma :=
          DirectedHomOrder.of_acyclicNonzeroNonisomorphisms sigma H
        have hxy : x < y :=
          lt_of_seed_irreducible_of_cross_height_le sigma H D
            huv hxu hyv (by omega)
        exact False.elim ((not_lt_of_ge
          (HO.lt_of_irreducible hyx).le) hxy)
      · intro hoffset
        omega
    · let yn : sigma.NoninjectiveLabel := ⟨y, hyInjective⟩
      have hSuccYOrbit : arOrbitLabel sigma H D
          (arSuccessor sigma D yn).1 = arOrbitLabel sigma H D v :=
        (arSuccessor_orbitLabel sigma H D yn).trans hyv
      have hSuccYHeight := arSuccessor_height sigma H D yn
      rw [arSuccessor_incidence sigma D yn x]
      rw [irreducible_same_orientation_iff_height_offset sigma H D
        huv hxu hSuccYOrbit]
      change arHeight sigma D (arSuccessor sigma D yn).1 =
        arHeight sigma D y + 1 at hSuccYHeight
      omega
  · let xp : sigma.NonprojectiveLabel := ⟨x, hxProjective⟩
    have hTauXOrbit : arOrbitLabel sigma H D
        (D.arTranslation sigma xp).1 = arOrbitLabel sigma H D u :=
      (arOrbitLabel_translation sigma H D xp).trans hxu
    have hTauXHeight := arHeight_translation sigma H D xp
    rw [D.arTranslation_incidence sigma xp y]
    rw [irreducible_same_orientation_iff_height_offset sigma H D
      huv hTauXOrbit hyv]
    change arHeight sigma D x =
      arHeight sigma D (D.arTranslation sigma xp).1 + 1 at hTauXHeight
    omega

/-- An irreducible seed arrow necessarily joins two distinct translation
orbits. -/
theorem seed_arOrbitLabel_ne
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) {u v : Iota}
    (huv : HasIrreducibleMorphism (sigma.obj u) (sigma.obj v)) :
    arOrbitLabel sigma H D u ≠ arOrbitLabel sigma H D v := by
  intro huvOrbit
  exact not_irreducible_of_same_arOrbitLabel sigma H D huvOrbit huv

/-- Paper-facing fixed-offset package for two translation orbits.  A seed
arrow joins distinct orbits; its orientation occupies one height diagonal,
the reverse orientation occupies the immediately adjacent diagonal, and
there are no irreducible arrows within either orbit. -/
theorem directed_two_arOrbits
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : ARData sigma) {u v : Iota}
    (huv : HasIrreducibleMorphism (sigma.obj u) (sigma.obj v)) :
    arOrbitLabel sigma H D u ≠ arOrbitLabel sigma H D v ∧
      (∀ {x y : Iota},
        arOrbitLabel sigma H D x = arOrbitLabel sigma H D u →
        arOrbitLabel sigma H D y = arOrbitLabel sigma H D v →
        (HasIrreducibleMorphism (sigma.obj x) (sigma.obj y) ↔
          arHeight sigma D x + arHeight sigma D v =
            arHeight sigma D y + arHeight sigma D u)) ∧
      (∀ {x y : Iota},
        arOrbitLabel sigma H D x = arOrbitLabel sigma H D u →
        arOrbitLabel sigma H D y = arOrbitLabel sigma H D v →
        (HasIrreducibleMorphism (sigma.obj y) (sigma.obj x) ↔
          arHeight sigma D y + arHeight sigma D u + 1 =
            arHeight sigma D x + arHeight sigma D v)) ∧
      (∀ {x y : Iota},
        arOrbitLabel sigma H D x = arOrbitLabel sigma H D y →
        ¬ HasIrreducibleMorphism (sigma.obj x) (sigma.obj y)) := by
  refine ⟨seed_arOrbitLabel_ne sigma H D huv, ?_, ?_, ?_⟩
  · intro x y hxu hyv
    exact irreducible_same_orientation_iff_height_offset
      sigma H D huv hxu hyv
  · intro x y hxu hyv
    exact irreducible_reverse_orientation_iff_height_offset
      sigma H D huv hxu hyv
  · intro x y hxy
    exact not_irreducible_of_same_arOrbitLabel sigma H D hxy

/-! ## Explicit directed-order comparisons

All translation-orbit and incidence assertions above are intrinsic.  Only
the comparison of vertices uses a chosen linear extension, so we expose that
small dependency for the reverse order supplied by opposite duality.
-/

/-- The weak cross-height inequality gives forward order for every supplied
directed Hom order. -/
theorem lt_of_seed_irreducible_of_cross_height_leFor [LinearOrder Iota]
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (HO : DirectedHomOrder sigma)
    (D : ARData sigma) {u v x y : Iota}
    (huv : HasIrreducibleMorphism (sigma.obj u) (sigma.obj v))
    (hxu : arOrbitLabel sigma H D x = arOrbitLabel sigma H D u)
    (hyv : arOrbitLabel sigma H D y = arOrbitLabel sigma H D v)
    (hcross : arHeight sigma D x + arHeight sigma D v ≤
      arHeight sigma D y + arHeight sigma D u) :
    x < y := by
  let t : ℕ := arHeight sigma D y + arHeight sigma D u -
    arHeight sigma D v
  have hvle : arHeight sigma D v ≤
      arHeight sigma D y + arHeight sigma D u := by omega
  have htEq : t + arHeight sigma D v =
      arHeight sigma D y + arHeight sigma D u := by
    exact Nat.sub_add_cancel hvle
  have hxt : arHeight sigma D x ≤ t := by omega
  obtain ⟨ur, hurInjective, huur⟩ :=
    exists_injective_descendant sigma H D u
  have huUrOrbit : arOrbitLabel sigma H D u = arOrbitLabel sigma H D ur :=
    arOrbitLabel_eq_of_reaches sigma H D huur
  have huUrHeight : arHeight sigma D u ≤ arHeight sigma D ur :=
    arHeight_le_of_arReach sigma D huur
  by_cases htur : t ≤ arHeight sigma D ur
  · obtain ⟨ut, hutUrOrbit, hutHeight⟩ :=
      exists_arOrbitLabel_eq_arHeight_eq_of_le sigma H D ur t htur
    have huUtOrbit : arOrbitLabel sigma H D u =
        arOrbitLabel sigma H D ut := huUrOrbit.trans hutUrOrbit.symm
    have hvYOrbit : arOrbitLabel sigma H D v =
        arOrbitLabel sigma H D y := hyv.symm
    have hutY : HasIrreducibleMorphism (sigma.obj ut) (sigma.obj y) := by
      by_cases hut : arHeight sigma D u ≤ t
      · let n := t - arHeight sigma D u
        apply irreducible_diagonal_forward sigma H D huv huUtOrbit hvYOrbit n
        · omega
        · omega
      · let n := arHeight sigma D u - t
        apply irreducible_diagonal_backward sigma H D huv huUtOrbit hvYOrbit n
        · omega
        · omega
    have hxUtOrbit : arOrbitLabel sigma H D x =
        arOrbitLabel sigma H D ut := hxu.trans huUtOrbit
    have hxUtHeight : arHeight sigma D x ≤ arHeight sigma D ut := by
      rw [hutHeight]
      exact hxt
    have hxUtReach := arReach_of_arOrbitLabel_eq_of_arHeight_le
      sigma H D hxUtOrbit hxUtHeight
    exact (arReach_leFor sigma HO D hxUtReach).trans_lt
      (HO.lt_of_irreducible hutY)
  · have hurt : arHeight sigma D ur < t := by omega
    let n := arHeight sigma D ur - arHeight sigma D u
    let l := arHeight sigma D v + n
    have hlY : l ≤ arHeight sigma D y := by omega
    obtain ⟨vl, hvlYOrbit, hvlHeight⟩ :=
      exists_arOrbitLabel_eq_arHeight_eq_of_le sigma H D y l hlY
    have hvVlOrbit : arOrbitLabel sigma H D v =
        arOrbitLabel sigma H D vl := hyv.symm.trans hvlYOrbit.symm
    have hurVl : HasIrreducibleMorphism (sigma.obj ur) (sigma.obj vl) := by
      apply irreducible_diagonal_forward sigma H D huv huUrOrbit hvVlOrbit n
      · omega
      · omega
    have hxUrReach := arReach_to_injective_of_arOrbitLabel_eq sigma H D
      hurInjective (hxu.trans huUrOrbit)
    have hvlYReach := arReach_of_arOrbitLabel_eq_of_arHeight_le
      sigma H D hvlYOrbit (by omega)
    exact ((arReach_leFor sigma HO D hxUrReach).trans_lt
      (HO.lt_of_irreducible hurVl)).trans_le
      (arReach_leFor sigma HO D hvlYReach)

/-- The complementary strict cross-height inequality gives reverse order
for every supplied directed Hom order. -/
theorem lt_of_seed_irreducible_of_cross_height_gtFor [LinearOrder Iota]
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (HO : DirectedHomOrder sigma)
    (D : ARData sigma) {u v x y : Iota}
    (huv : HasIrreducibleMorphism (sigma.obj u) (sigma.obj v))
    (hxu : arOrbitLabel sigma H D x = arOrbitLabel sigma H D u)
    (hyv : arOrbitLabel sigma H D y = arOrbitLabel sigma H D v)
    (hcross : arHeight sigma D y + arHeight sigma D u <
      arHeight sigma D x + arHeight sigma D v) :
    y < x := by
  by_cases huInjective : Injective (sigma.obj u)
  · have hxuReach := arReach_to_injective_of_arOrbitLabel_eq sigma H D
      huInjective hxu
    have hxuHeight : arHeight sigma D x ≤ arHeight sigma D u :=
      arHeight_le_of_arReach sigma D hxuReach
    have hvpos : 0 < arHeight sigma D v := by omega
    let vp : sigma.NonprojectiveLabel :=
      ⟨v, (arHeight_pos_iff_nonprojective sigma H D v).mp hvpos⟩
    have hback : HasIrreducibleMorphism
        (sigma.obj (D.arTranslation sigma vp).1) (sigma.obj u) :=
      (D.arTranslation_incidence sigma vp u).1 huv
    have hyTauV : arOrbitLabel sigma H D y =
        arOrbitLabel sigma H D (D.arTranslation sigma vp).1 :=
      hyv.trans (arOrbitLabel_translation sigma H D vp).symm
    have hvHeight := arHeight_translation sigma H D vp
    change arHeight sigma D v =
      arHeight sigma D (D.arTranslation sigma vp).1 + 1 at hvHeight
    exact lt_of_seed_irreducible_of_cross_height_leFor sigma H HO D
      hback hyTauV hxu (by omega)
  · let un : sigma.NoninjectiveLabel := ⟨u, huInjective⟩
    have hforward : HasIrreducibleMorphism (sigma.obj v)
        (sigma.obj (arSuccessor sigma D un).1) :=
      (arSuccessor_incidence sigma D un v).1 huv
    have hxSuccU : arOrbitLabel sigma H D x =
        arOrbitLabel sigma H D (arSuccessor sigma D un).1 :=
      hxu.trans (arSuccessor_orbitLabel sigma H D un).symm
    have huHeight := arSuccessor_height sigma H D un
    change arHeight sigma D (arSuccessor sigma D un).1 =
      arHeight sigma D u + 1 at huHeight
    exact lt_of_seed_irreducible_of_cross_height_leFor sigma H HO D
      hforward hyv hxSuccU (by omega)

/-- Exact weak cross-height criterion for an arbitrary supplied directed
Hom order. -/
theorem lt_iff_seed_cross_height_leFor [LinearOrder Iota]
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (HO : DirectedHomOrder sigma)
    (D : ARData sigma) {u v x y : Iota}
    (huv : HasIrreducibleMorphism (sigma.obj u) (sigma.obj v))
    (hxu : arOrbitLabel sigma H D x = arOrbitLabel sigma H D u)
    (hyv : arOrbitLabel sigma H D y = arOrbitLabel sigma H D v) :
    x < y ↔ arHeight sigma D x + arHeight sigma D v ≤
      arHeight sigma D y + arHeight sigma D u := by
  constructor
  · intro hxy
    by_contra hnot
    have hyx := lt_of_seed_irreducible_of_cross_height_gtFor
      sigma H HO D huv hxu hyv (by omega)
    exact lt_asymm hxy hyx
  · exact lt_of_seed_irreducible_of_cross_height_leFor
      sigma H HO D huv hxu hyv

/-- Exact strict reverse cross-height criterion for an arbitrary supplied
directed Hom order. -/
theorem reverse_lt_iff_seed_cross_height_gtFor [LinearOrder Iota]
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (HO : DirectedHomOrder sigma)
    (D : ARData sigma) {u v x y : Iota}
    (huv : HasIrreducibleMorphism (sigma.obj u) (sigma.obj v))
    (hxu : arOrbitLabel sigma H D x = arOrbitLabel sigma H D u)
    (hyv : arOrbitLabel sigma H D y = arOrbitLabel sigma H D v) :
    y < x ↔ arHeight sigma D y + arHeight sigma D u <
      arHeight sigma D x + arHeight sigma D v := by
  constructor
  · intro hyx
    by_contra hnot
    have hxy := lt_of_seed_irreducible_of_cross_height_leFor
      sigma H HO D huv hxu hyv (by omega)
    exact lt_asymm hyx hxy
  · exact lt_of_seed_irreducible_of_cross_height_gtFor
      sigma H HO D huv hxu hyv

end QuotientSubmoduleEquidistribution.RepresentationDirected.DirectedAROrbit.TwoOrbits
