import OpConjecture.RepresentationDirected.SimpleGraphWordRoots

/-!
# Reduction of root-sign compatibility to one descent direction

For the graph geometric representation, the usual equivalence

`w α_i` positive iff `i` is not a right descent of `w`

is equivalent to its apparently weaker descent-to-negativity direction.  The
reverse direction follows by applying that direction to `w s_i`, because both
the descent status and the root sign toggle.
-/

noncomputable section

namespace OpConjecture.RepresentationDirected.RootSignStrategy

open SimpleGraphCoxeter WordRootProcess

universe u

variable {L : Type u} [Fintype L]

/-- The one-way geometric input needed for the full root-sign criterion. -/
def RightDescentImpliesNegativeRoot (G : SimpleGraph L) : Prop :=
  ∀ (w : Group G) (i : L),
    (system G).IsRightDescent w i →
      IsNegative (geometricRepresentation G w (simpleRoot i))

/-- The global, elementwise form of root-sign/right-descent compatibility. -/
def HasGlobalRootSignCompatibility (G : SimpleGraph L) : Prop :=
  ∀ (w : Group G) (i : L),
    IsPositive (geometricRepresentation G w (simpleRoot i)) ↔
      ¬ (system G).IsRightDescent w i

/-- The one geometric half of the usual reduced-word/root criterion. -/
def ReducedWordsHavePositiveInversionRoots (G : SimpleGraph L) : Prop :=
  ∀ Q : List L,
    IsReduced G Q → HasPositiveInversionRoots G Q

/-- Every real root of the graph representation lies in one of the two
coordinate cones. -/
def HasRealRootSignDichotomy (G : SimpleGraph L) : Prop :=
  ∀ (w : Group G) (i : L),
    IsPositive (geometricRepresentation G w (simpleRoot i)) ∨
      IsNegative (geometricRepresentation G w (simpleRoot i))

/-- Transporting a simple root transports its reflection inside the
presented Coxeter group.  Faithfulness of the geometric representation,
together with invariance of its Cartan form, implies this statement. -/
def RootTransportDeterminesReflection (G : SimpleGraph L) : Prop :=
  ∀ (w : Group G) (i j : L),
    geometricRepresentation G w (simpleRoot i) = simpleRoot j →
      w * (system G).simple i = (system G).simple j * w

/-- Right multiplication by `s_i` negates the image of `α_i`. -/
theorem geometricRepresentation_mul_simple_simpleRoot
    (G : SimpleGraph L) (w : Group G) (i : L) :
    geometricRepresentation G (w * (system G).simple i) (simpleRoot i) =
      -geometricRepresentation G w (simpleRoot i) := by
  rw [map_mul, LinearEquiv.mul_apply, geometricRepresentation_simple]
  change
    geometricRepresentation G w (simpleReflection G i (simpleRoot i)) =
      -geometricRepresentation G w (simpleRoot i)
  rw [simpleReflection_simpleRoot_self]
  exact map_neg (geometricRepresentation G w) (simpleRoot i)

/-- A simple reflection can send a positive real root to a negative vector
only when that root is the reflecting simple root.  The coordinate argument
shows that the root is a positive multiple of `α_i`; integrality and the
fact that a real root is the image of a basis vector under a lattice
automorphism force that multiple to be one. -/
theorem eq_simpleRoot_of_positive_of_simpleReflection_negative
    (G : SimpleGraph L) (w : Group G) (j i : L)
    (hpos :
      IsPositive (geometricRepresentation G w (simpleRoot j)))
    (hneg :
      IsNegative
        (simpleReflection G i
          (geometricRepresentation G w (simpleRoot j)))) :
    geometricRepresentation G w (simpleRoot j) = simpleRoot i := by
  let z : RootLattice L := geometricRepresentation G w (simpleRoot j)
  have hoff : ∀ h, h ≠ i → z h = 0 := by
    intro h hhi
    have hzle := hneg.1 h
    rw [simpleReflection_apply_of_ne G hhi] at hzle
    exact le_antisymm hzle (hpos.1 h)
  have hzi_ne : z i ≠ 0 := by
    intro hzi
    apply hpos.2
    funext h
    by_cases hhi : h = i
    · subst h
      exact hzi
    · exact hoff h hhi
  have hzi_pos : 0 < z i := lt_of_le_of_ne (hpos.1 i) (Ne.symm hzi_ne)
  have hzsmul : z = (z i) • simpleRoot i := by
    funext h
    by_cases hhi : h = i
    · subst h
      simp
    · simp [hoff h hhi, simpleRoot_apply_of_ne hhi]
  have hinv :=
    congrArg (fun y ↦ (geometricRepresentation G w).symm y) hzsmul
  have hmul :
      z i * ((geometricRepresentation G w).symm (simpleRoot i)) j = 1 := by
    have hj := congrFun hinv j
    simpa only [z, LinearEquiv.symm_apply_apply, map_zsmul, Pi.smul_apply,
      smul_eq_mul, simpleRoot_apply_self] using hj.symm
  have hdiv : z i ∣ 1 :=
    ⟨((geometricRepresentation G w).symm (simpleRoot i)) j, hmul.symm⟩
  have hzi_one : z i = 1 := Int.eq_one_of_dvd_one hzi_pos.le hdiv
  change z = simpleRoot i
  rw [hzsmul, hzi_one, one_smul]

/-- The action of a word with a head letter applies the head reflection
after the action of its tail. -/
theorem geometricRepresentation_wordProd_cons
    (G : SimpleGraph L) (a : L) (Q : List L) (z : RootLattice L) :
    geometricRepresentation G (wordProd G (a :: Q)) z =
      simpleReflection G a (geometricRepresentation G (wordProd G Q) z) := by
  unfold SimpleGraphCoxeter.wordProd
  rw [CoxeterSystem.wordProd_cons, map_mul, LinearEquiv.mul_apply,
    geometricRepresentation_simple]
  rfl

/-- Sign dichotomy and reflection transport give the geometric deletion
step: if a word sends `α_i` negative, appending `i` has the same product as
deleting one letter of the original word. -/
theorem exists_eraseIdx_of_wordRoot_negative
    (G : SimpleGraph L)
    (hsign : HasRealRootSignDichotomy G)
    (htransport : RootTransportDeterminesReflection G)
    (Q : List L) (i : L)
    (hnegative :
      IsNegative (geometricRepresentation G (wordProd G Q) (simpleRoot i))) :
    ∃ k, k < Q.length ∧
      wordProd G (Q.concat i) = wordProd G (Q.eraseIdx k) := by
  induction Q with
  | nil =>
      exfalso
      exact simpleRoot_isPositive i |>.not_isNegative
        (by simpa [SimpleGraphCoxeter.wordProd] using hnegative)
  | cons a Q ih =>
      have houter :
          IsNegative
            (simpleReflection G a
              (geometricRepresentation G (wordProd G Q) (simpleRoot i))) := by
        simpa only [geometricRepresentation_wordProd_cons] using hnegative
      rcases hsign (wordProd G Q) i with hpositive | hnegativeTail
      · have hroot :
            geometricRepresentation G (wordProd G Q) (simpleRoot i) =
              simpleRoot a :=
          eq_simpleRoot_of_positive_of_simpleReflection_negative
            G (wordProd G Q) i a hpositive houter
        have hmove := htransport (wordProd G Q) i a hroot
        refine ⟨0, by simp, ?_⟩
        simp only [List.concat_cons, List.eraseIdx_zero, List.tail_cons]
        unfold SimpleGraphCoxeter.wordProd
        rw [(system G).wordProd_cons, (system G).wordProd_concat]
        change
          (system G).wordProd Q * (system G).simple i =
            (system G).simple a * (system G).wordProd Q at hmove
        rw [hmove]
        exact (system G).simple_mul_simple_cancel_left a
      · obtain ⟨k, hk, hkprod⟩ := ih hnegativeTail
        refine ⟨k + 1, by simp [hk], ?_⟩
        have hmul :=
          congrArg (fun x ↦ (system G).simple a * x) hkprod
        simpa only [List.concat_cons, List.eraseIdx_cons_succ,
          SimpleGraphCoxeter.wordProd, CoxeterSystem.wordProd_cons] using hmul

/-- A reduced one-letter extension cannot have a negative last inversion
root: the geometric deletion step would represent it by a word shorter by
two letters. -/
theorem not_wordRoot_negative_of_isReduced_concat
    (G : SimpleGraph L)
    (hsign : HasRealRootSignDichotomy G)
    (htransport : RootTransportDeterminesReflection G)
    (Q : List L) (i : L)
    (hred : IsReduced G (Q.concat i)) :
    ¬ IsNegative
      (geometricRepresentation G (wordProd G Q) (simpleRoot i)) := by
  intro hnegative
  obtain ⟨k, hk, hkprod⟩ :=
    exists_eraseIdx_of_wordRoot_negative G hsign htransport Q i hnegative
  have hle := (system G).length_wordProd_le (Q.eraseIdx k)
  have hredEq := hred.eq
  change
    (system G).length ((system G).wordProd (Q.concat i)) =
      (Q.concat i).length at hredEq
  change
    (system G).wordProd (Q.concat i) =
      (system G).wordProd (Q.eraseIdx k) at hkprod
  rw [hkprod, List.length_concat] at hredEq
  have herase := List.length_eraseIdx_add_one hk
  omega

/-- The two structural Tits-representation facts—real-root sign dichotomy
and transport of reflections by their roots—imply positivity of every
inversion root of every reduced word. -/
theorem reducedWordsHavePositiveInversionRoots_of_signDichotomy_of_rootTransport
    (G : SimpleGraph L)
    (hsign : HasRealRootSignDichotomy G)
    (htransport : RootTransportDeterminesReflection G) :
    ReducedWordsHavePositiveInversionRoots G := by
  intro Q hred x
  have htake := hred.take (x + 1)
  have hlist : (Q.take x).concat Q[x] = Q.take (x + 1) :=
    by
      rw [List.concat_eq_append]
      exact List.take_concat_get' Q x x.isLt
  have hconcat : IsReduced G ((Q.take x).concat Q[x]) := by
    unfold SimpleGraphCoxeter.IsReduced
    rw [hlist]
    exact htake
  rcases hsign (wordProd G (Q.take x)) Q[x] with hpositive | hnegative
  · simpa [inversionRoot, prefixElement, SimpleGraphCoxeter.wordProd] using hpositive
  · exact False.elim
      (not_wordRoot_negative_of_isReduced_concat G hsign htransport
        (Q.take x) Q[x] hconcat hnegative)

/-- The one-way descent-to-negative-root statement already gives the full
root-sign/right-descent equivalence. -/
theorem hasGlobalRootSignCompatibility_of_rightDescentImpliesNegativeRoot
    (G : SimpleGraph L)
    (hneg : RightDescentImpliesNegativeRoot G) :
    HasGlobalRootSignCompatibility G := by
  intro w i
  constructor
  · intro hpos hdescent
    exact IsPositive.not_isNegative hpos (hneg w i hdescent)
  · intro hnot
    have hdescent :
        (system G).IsRightDescent (w * (system G).simple i) i := by
      rw [(system G).isRightDescent_iff_not_isRightDescent_mul]
      simpa only [(system G).simple_mul_simple_cancel_right] using hnot
    have hnegative := hneg (w * (system G).simple i) i hdescent
    rw [geometricRepresentation_mul_simple_simpleRoot] at hnegative
    simpa using hnegative.neg

/-- Conversely, full compatibility gives descent-to-negativity by toggling
at `w s_i`. -/
theorem rightDescentImpliesNegativeRoot_of_hasGlobalRootSignCompatibility
    (G : SimpleGraph L)
    (hcompat : HasGlobalRootSignCompatibility G) :
    RightDescentImpliesNegativeRoot G := by
  intro w i hdescent
  have hnot :
      ¬ (system G).IsRightDescent (w * (system G).simple i) i :=
    ((system G).isRightDescent_iff_not_isRightDescent_mul).mp hdescent
  have hpositive := (hcompat (w * (system G).simple i) i).2 hnot
  rw [geometricRepresentation_mul_simple_simpleRoot] at hpositive
  simpa using hpositive.neg

/-- The one-way and two-way global formulations are equivalent. -/
theorem rightDescentImpliesNegativeRoot_iff_globalCompatibility
    (G : SimpleGraph L) :
    RightDescentImpliesNegativeRoot G ↔
      HasGlobalRootSignCompatibility G :=
  ⟨hasGlobalRootSignCompatibility_of_rightDescentImpliesNegativeRoot G,
    rightDescentImpliesNegativeRoot_of_hasGlobalRootSignCompatibility G⟩

/-- Positivity of inversion roots for reduced words implies the one-way
descent-to-negative-root theorem.  For a descent of `w` at `i`, take a
reduced word for `w s_i`; appending `i` is reduced and its last inversion
root is positive, while multiplication by `s_i` negates that root. -/
theorem rightDescentImpliesNegativeRoot_of_reducedWordsPositive
    (G : SimpleGraph L)
    (hpositive : ReducedWordsHavePositiveInversionRoots G) :
    RightDescentImpliesNegativeRoot G := by
  intro w i hdescent
  let v : Group G := w * (system G).simple i
  obtain ⟨Q, hQ, hv⟩ := (system G).exists_isReduced v
  have hlength : (system G).length v + 1 = (system G).length w := by
    simpa only [v] using (system G).isRightDescent_iff.mp hdescent
  have hvsi : v * (system G).simple i = w := by
    dsimp only [v]
    exact (system G).simple_mul_simple_cancel_right i
  have hconcat : IsReduced G (Q.concat i) := by
    unfold SimpleGraphCoxeter.IsReduced CoxeterSystem.IsReduced
    rw [(system G).wordProd_concat, ← hv, hvsi, List.length_concat,
      ← hQ.eq, ← hv]
    exact hlength.symm
  have hlast :=
    hpositive (Q.concat i) hconcat ⟨Q.length, by simp⟩
  rw [inversionRoot_concat_last] at hlast
  change
    IsPositive
      (geometricRepresentation G ((system G).wordProd Q) (simpleRoot i))
    at hlast
  rw [← hv] at hlast
  have hwroot :
      geometricRepresentation G w (simpleRoot i) =
        -geometricRepresentation G v (simpleRoot i) := by
    rw [← hvsi, geometricRepresentation_mul_simple_simpleRoot]
  rw [hwroot]
  exact hlast.neg

/-- The reduced-word positivity theorem also supplies sign dichotomy for
every real root: use the descent branch for negativity and the complementary
branch of global compatibility for positivity. -/
theorem hasRealRootSignDichotomy_of_reducedWordsPositive
    (G : SimpleGraph L)
    (hpositive : ReducedWordsHavePositiveInversionRoots G) :
    HasRealRootSignDichotomy G := by
  let hneg : RightDescentImpliesNegativeRoot G :=
    rightDescentImpliesNegativeRoot_of_reducedWordsPositive G hpositive
  let hcompat : HasGlobalRootSignCompatibility G :=
    hasGlobalRootSignCompatibility_of_rightDescentImpliesNegativeRoot G hneg
  intro w i
  by_cases hdescent : (system G).IsRightDescent w i
  · exact Or.inr (hneg w i hdescent)
  · exact Or.inl ((hcompat w i).2 hdescent)

/-- Conversely, descent-to-negativity gives positivity of every inversion
root of every reduced word. -/
theorem reducedWordsHavePositiveInversionRoots_of_rightDescentNegativity
    (G : SimpleGraph L)
    (hneg : RightDescentImpliesNegativeRoot G) :
    ReducedWordsHavePositiveInversionRoots G := by
  intro Q hQ
  exact
    (isReduced_iff_hasPositiveInversionRoots G Q
      (fun x ↦
        hasGlobalRootSignCompatibility_of_rightDescentImpliesNegativeRoot G hneg
          (prefixElement G Q x) Q[x])).mp hQ

/-- Thus the single geometric statement "reduced words have positive
inversion roots" is equivalent to the full global sign/descent theorem. -/
theorem reducedWordsPositive_iff_globalCompatibility
    (G : SimpleGraph L) :
    ReducedWordsHavePositiveInversionRoots G ↔
      HasGlobalRootSignCompatibility G :=
  ⟨fun h ↦
      hasGlobalRootSignCompatibility_of_rightDescentImpliesNegativeRoot G
        (rightDescentImpliesNegativeRoot_of_reducedWordsPositive G h),
    fun h ↦
      reducedWordsHavePositiveInversionRoots_of_rightDescentNegativity G
        (rightDescentImpliesNegativeRoot_of_hasGlobalRootSignCompatibility G h)⟩

/-- Global compatibility supplies the exact word-prefix datum used by the
representation-directed development. -/
theorem hasPrefixRootSignCompatibility_of_global
    (G : SimpleGraph L) (Q : List L)
    (hcompat : HasGlobalRootSignCompatibility G) :
    HasPrefixRootSignCompatibility G Q := by
  intro x
  exact hcompat (prefixElement G Q x) Q[x]

/-- Therefore the standard positive-inversion-root reducedness criterion
needs only the one-way descent-to-negative-root theorem. -/
theorem isReduced_iff_hasPositiveInversionRoots_of_rightDescentNegativity
    (G : SimpleGraph L) (Q : List L)
    (hneg : RightDescentImpliesNegativeRoot G) :
    IsReduced G Q ↔ HasPositiveInversionRoots G Q :=
  isReduced_iff_hasPositiveInversionRoots G Q
    (hasPrefixRootSignCompatibility_of_global G Q
      (hasGlobalRootSignCompatibility_of_rightDescentImpliesNegativeRoot G hneg))

end OpConjecture.RepresentationDirected.RootSignStrategy
