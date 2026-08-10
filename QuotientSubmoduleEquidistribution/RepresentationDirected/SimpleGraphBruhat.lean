import QuotientSubmoduleEquidistribution.RepresentationDirected.FixedWordProfile
import Mathlib.Data.Fin.Tuple.Take
import Mathlib.Data.List.NodupEquivFin

/-!
# Strong exchange and intrinsic Bruhat order for a finite simple graph

This file upgrades the unconditional simple exchange theorem to arbitrary
reflections.  A reflection is first represented by a positive real root.  If
the inverse word sends that root negative, the first sign change locates the
letter deleted by strong exchange.  Strong exchange then proves the full
Bruhat subword theorem, the principal-interval equivalence, and the exact
fixed-word reverse-length profile.
-/

set_option autoImplicit false

noncomputable section

namespace QuotientSubmoduleEquidistribution.RepresentationDirected.SimpleGraphBruhat

open QuotientSubmoduleEquidistribution.RepresentationDirected.FixedWord
open FixedWordSubwords
open FixedWordProfile
open Polynomial
open SimpleGraphCoxeter WordRootProcess RootSignStrategy SortingExchange

universe uL

variable {L : Type uL} [Fintype L]

/-- Every reflection admits a conjugating witness whose associated real root
is positive. -/
theorem exists_positiveRoot_witness_of_isReflection
    (G : SimpleGraph L) {t : Group G}
    (ht : (system G).IsReflection t) :
    ∃ x : Group G, ∃ i : L,
      t = x * (system G).simple i * x⁻¹ ∧
        IsPositive
          (geometricRepresentation G x (simpleRoot i)) := by
  obtain ⟨x, i, rfl⟩ := ht
  rcases realRootSignDichotomy G x i with hpos | hneg
  · exact ⟨x, i, rfl, hpos⟩
  · refine ⟨x * (system G).simple i, i, ?_, ?_⟩
    · group
    · rw [geometricRepresentation_mul_simple_simpleRoot]
      exact hneg.neg

/-- If a positive real root becomes negative while a word is processed from
left to right, then immediately before some letter it is that letter's
simple root. -/
theorem exists_split_of_positiveRoot_to_negative
    (G : SimpleGraph L) (Q : List L)
    (x : Group G) (i : L)
    (hpos : IsPositive
      (geometricRepresentation G x (simpleRoot i)))
    (hneg : IsNegative
      (reflectInIncreasingOrder G Q
        (geometricRepresentation G x (simpleRoot i)))) :
    ∃ pre : List L, ∃ a : L, ∃ post : List L,
      Q = pre ++ a :: post ∧
        reflectInIncreasingOrder G pre
          (geometricRepresentation G x (simpleRoot i)) =
            simpleRoot a := by
  induction Q generalizing x with
  | nil =>
      exact False.elim (hpos.not_isNegative (by simpa using hneg))
  | cons a Q ih =>
      have hstep :
          simpleReflection G a
              (geometricRepresentation G x (simpleRoot i)) =
            geometricRepresentation G
              ((system G).simple a * x) (simpleRoot i) := by
        rw [map_mul, LinearEquiv.mul_apply,
          geometricRepresentation_simple]
        rfl
      rcases realRootSignDichotomy G
          ((system G).simple a * x) i with hnextPos | hnextNeg
      · have htailNeg :
            IsNegative
              (reflectInIncreasingOrder G Q
                (geometricRepresentation G
                  ((system G).simple a * x) (simpleRoot i))) := by
          simpa only [reflectInIncreasingOrder_cons, hstep] using hneg
        obtain ⟨pre, b, post, hQ, hroot⟩ :=
          ih ((system G).simple a * x) hnextPos htailNeg
        refine ⟨a :: pre, b, post, ?_, ?_⟩
        · simp [hQ]
        · simpa only [reflectInIncreasingOrder_cons, hstep] using hroot
      · have hnextNeg' :
            IsNegative
              (simpleReflection G a
                (geometricRepresentation G x (simpleRoot i))) := by
          simpa only [hstep] using hnextNeg
        have hroot :=
          eq_simpleRoot_of_positive_of_simpleReflection_negative
            G x i a hpos hnextNeg'
        exact ⟨[], a, Q, by simp, by simpa using hroot⟩

/-- Equality of two transported simple roots identifies the corresponding
conjugate reflections. -/
theorem conjugate_simple_eq_of_root_eq
    (G : SimpleGraph L) (x p : Group G) (i a : L)
    (hroot :
      geometricRepresentation G x (simpleRoot i) =
        geometricRepresentation G p (simpleRoot a)) :
    x * (system G).simple i * x⁻¹ =
      p * (system G).simple a * p⁻¹ := by
  have htransportRoot :
      geometricRepresentation G (p⁻¹ * x) (simpleRoot i) =
        simpleRoot a := by
    rw [map_mul, LinearEquiv.mul_apply, map_inv]
    apply (geometricRepresentation G p).injective
    simpa using hroot
  have hmove := rootTransportDeterminesReflection G
    (p⁻¹ * x) i a htransportRoot
  apply mul_right_cancel (b := x)
  apply mul_left_cancel (a := p⁻¹)
  simpa [mul_assoc] using hmove

/-- A positive real root sent negative by the inverse word action gives the
strong-exchange deletion identity for its reflection. -/
theorem exists_eraseIdx_of_positiveRoot_inverse_negative
    (G : SimpleGraph L) (Q : List L)
    (x : Group G) (i : L)
    (hpos : IsPositive
      (geometricRepresentation G x (simpleRoot i)))
    (hneg : IsNegative
      (geometricRepresentation G (wordProd G Q)⁻¹
        (geometricRepresentation G x (simpleRoot i)))) :
    ∃ k, k < Q.length ∧
      (x * (system G).simple i * x⁻¹) * wordProd G Q =
        wordProd G (Q.eraseIdx k) := by
  have hprocessNeg :
      IsNegative
        (reflectInIncreasingOrder G Q
          (geometricRepresentation G x (simpleRoot i))) := by
    simpa only [reflectInIncreasingOrder_eq_inverse_word_action,
      SimpleGraphCoxeter.wordProd] using hneg
  obtain ⟨pre, a, post, hQ, hrootProcess⟩ :=
    exists_split_of_positiveRoot_to_negative
      G Q x i hpos hprocessNeg
  have hroot :
      geometricRepresentation G x (simpleRoot i) =
        geometricRepresentation G (wordProd G pre) (simpleRoot a) := by
    rw [reflectInIncreasingOrder_eq_inverse_word_action] at hrootProcess
    calc
      geometricRepresentation G x (simpleRoot i) =
          geometricRepresentation G (wordProd G pre)
            (geometricRepresentation G (wordProd G pre)⁻¹
              (geometricRepresentation G x (simpleRoot i))) := by
        simp
      _ = geometricRepresentation G (wordProd G pre)
          (simpleRoot a) := congrArg
            (geometricRepresentation G (wordProd G pre)) hrootProcess
  have hreflection :=
    conjugate_simple_eq_of_root_eq G x (wordProd G pre) i a hroot
  refine ⟨pre.length, ?_, ?_⟩
  · simp [hQ]
  · rw [hreflection, hQ, List.eraseIdx_eq_take_drop_succ]
    simp [SimpleGraphCoxeter.wordProd,
      CoxeterSystem.wordProd_append,
      CoxeterSystem.wordProd_cons, mul_assoc]
    exact (system G).simple_mul_simple_cancel_left
      (w := (system G).wordProd post) a

/-- A conjugate simple reflection negates its transported simple root. -/
theorem geometricRepresentation_conjugate_simple_negates_root
    (G : SimpleGraph L) (x : Group G) (i : L) :
    geometricRepresentation G
        (x * (system G).simple i * x⁻¹)
        (geometricRepresentation G x (simpleRoot i)) =
      -geometricRepresentation G x (simpleRoot i) := by
  have hxinv :
      geometricRepresentation G x⁻¹
          (geometricRepresentation G x (simpleRoot i)) =
        simpleRoot i := by
    calc
      geometricRepresentation G x⁻¹
          (geometricRepresentation G x (simpleRoot i)) =
          geometricRepresentation G (x⁻¹ * x) (simpleRoot i) := by
        rw [map_mul, LinearEquiv.mul_apply]
      _ = simpleRoot i := by simp
  calc
    geometricRepresentation G
        (x * (system G).simple i * x⁻¹)
        (geometricRepresentation G x (simpleRoot i)) =
        geometricRepresentation G x
          (geometricRepresentation G ((system G).simple i)
            (geometricRepresentation G x⁻¹
              (geometricRepresentation G x (simpleRoot i)))) := by
      rw [map_mul, map_mul, LinearEquiv.mul_apply,
        LinearEquiv.mul_apply]
    _ = geometricRepresentation G x
        (simpleReflection G i (simpleRoot i)) := by
      rw [hxinv, geometricRepresentation_simple]
      rfl
    _ = -geometricRepresentation G x (simpleRoot i) := by
      rw [simpleReflection_simpleRoot_self, map_neg]

/-- The root-sign crossing already implies the required strict length drop
when the ambient word is reduced. -/
theorem length_conjugate_simple_mul_lt_of_inverse_root_negative
    (G : SimpleGraph L) (Q : List L)
    (hQ : IsReduced G Q)
    (x : Group G) (i : L)
    (hpos : IsPositive
      (geometricRepresentation G x (simpleRoot i)))
    (hneg : IsNegative
      (geometricRepresentation G (wordProd G Q)⁻¹
        (geometricRepresentation G x (simpleRoot i)))) :
    (system G).length
        ((x * (system G).simple i * x⁻¹) * wordProd G Q) <
      (system G).length (wordProd G Q) := by
  unfold SimpleGraphCoxeter.IsReduced at hQ
  obtain ⟨k, hk, hdelete⟩ :=
    exists_eraseIdx_of_positiveRoot_inverse_negative
      G Q x i hpos hneg
  unfold SimpleGraphCoxeter.wordProd at hdelete ⊢
  rw [hdelete, hQ.eq]
  calc
    (system G).length (wordProd G (Q.eraseIdx k)) ≤
        (Q.eraseIdx k).length :=
      (system G).length_wordProd_le (Q.eraseIdx k)
    _ < Q.length := by
      rw [← List.length_eraseIdx_add_one hk]
      omega

/-- Left strong exchange for the graph Coxeter system. -/
def HasStrongLeftExchange (G : SimpleGraph L) : Prop :=
  ∀ (Q : List L), IsReduced G Q →
    ∀ (t : Group G), (system G).IsReflection t →
      (system G).length (t * wordProd G Q) <
          (system G).length (wordProd G Q) →
        ∃ k, k < Q.length ∧
          t * wordProd G Q = wordProd G (Q.eraseIdx k)

/-- Unconditional strong exchange, obtained by orienting a reflection root
positively.  If the inverse word sent that root positive, applying the same
negative-root deletion argument to `t w` would force the opposite strict
length inequality. -/
theorem hasStrongLeftExchange_simpleGraph
    (G : SimpleGraph L) : HasStrongLeftExchange G := by
  intro Q hQ t ht hlt
  obtain ⟨x, i, htEq, hpos⟩ :=
    exists_positiveRoot_witness_of_isReflection G ht
  let beta : RootLattice L :=
    geometricRepresentation G x (simpleRoot i)
  let w : Group G := wordProd G Q
  have hrootAction :
      geometricRepresentation G (w⁻¹ * x) (simpleRoot i) =
        geometricRepresentation G w⁻¹ beta := by
    simp [beta, map_mul, LinearEquiv.mul_apply]
  rcases realRootSignDichotomy G (w⁻¹ * x) i with
      hfinalPosRaw | hfinalNegRaw
  · have hfinalPos :
        IsPositive (geometricRepresentation G w⁻¹ beta) := by
      rw [← hrootAction]
      exact hfinalPosRaw
    let v : Group G := t * w
    obtain ⟨R, hR, hv⟩ := (system G).exists_isReduced v
    have htBeta :
        geometricRepresentation G t beta = -beta := by
      rw [htEq]
      exact geometricRepresentation_conjugate_simple_negates_root
        G x i
    have hvInvBeta :
        geometricRepresentation G v⁻¹ beta =
          -geometricRepresentation G w⁻¹ beta := by
      simp only [v, mul_inv_rev]
      rw [ht.inv, map_mul, LinearEquiv.mul_apply, htBeta, map_neg]
    have hRneg :
        IsNegative
          (geometricRepresentation G (wordProd G R)⁻¹ beta) := by
      change IsNegative
        (geometricRepresentation G ((system G).wordProd R)⁻¹ beta)
      rw [← hv, hvInvBeta]
      exact hfinalPos.neg
    have hreverse :
        (system G).length (t * wordProd G R) <
          (system G).length (wordProd G R) := by
      rw [htEq]
      exact length_conjugate_simple_mul_lt_of_inverse_root_negative
        G R hR x i hpos hRneg
    have hwrong :
        (system G).length w < (system G).length (t * w) := by
      change
        (system G).length (t * (system G).wordProd R) <
          (system G).length ((system G).wordProd R) at hreverse
      rw [← hv] at hreverse
      have httw : t * (t * w) = w := by
        rw [← mul_assoc, ht.mul_self, one_mul]
      rw [show v = t * w by rfl, httw] at hreverse
      exact hreverse
    have hlt' :
        (system G).length (t * w) < (system G).length w := by
      simpa [w] using hlt
    exact False.elim (Nat.lt_asymm hlt' hwrong)
  · have hfinalNeg :
        IsNegative (geometricRepresentation G w⁻¹ beta) := by
      rw [← hrootAction]
      exact hfinalNegRaw
    obtain ⟨k, hk, hdelete⟩ :=
      exists_eraseIdx_of_positiveRoot_inverse_negative
        G Q x i hpos (by simpa [w, beta] using hfinalNeg)
    exact ⟨k, hk, by simpa [htEq] using hdelete⟩

/-! ## Deletion reduction and the intrinsic Bruhat relation -/

/-- Two-letter deletion for graph-Coxeter words. -/
def HasDeletionCondition (G : SimpleGraph L) : Prop :=
  ∀ Q : List L, ¬ IsReduced G Q →
    ∃ A : List L, ∃ a : L, ∃ C : List L, ∃ b : L, ∃ E : List L,
      Q = A ++ a :: C ++ b :: E ∧
        wordProd G Q = wordProd G (A ++ C ++ E)

/-- Unconditional deletion, derived from production simple left exchange. -/
theorem hasDeletionCondition_simpleGraph
    (G : SimpleGraph L) : HasDeletionCondition G := by
  intro Q hQ
  induction Q with
  | nil =>
      exfalso
      apply hQ
      simp [SimpleGraphCoxeter.IsReduced, CoxeterSystem.IsReduced]
  | cons a R ih =>
      by_cases hR : IsReduced G R
      · have hdescent :
            (system G).IsLeftDescent (wordProd G R) a := by
          by_contra hnot
          apply hQ
          exact (isReduced_cons_iff_not_isLeftDescent
            (system G) R a hR).mpr hnot
        obtain ⟨pre, x, post, hsplit, hprod⟩ :=
          hasSimpleLeftExchange_simpleGraph G R a hR hdescent
        refine ⟨[], a, pre, x, post, ?_, ?_⟩
        · simp [hsplit]
        · simpa [SimpleGraphCoxeter.wordProd,
            CoxeterSystem.wordProd_cons] using hprod
      · obtain ⟨A, x, C, y, E, hsplit, hprod⟩ := ih hR
        refine ⟨a :: A, x, C, y, E, ?_, ?_⟩
        · simp [hsplit]
        · simpa [SimpleGraphCoxeter.wordProd,
            CoxeterSystem.wordProd_cons] using
            congrArg (fun z ↦ (system G).simple a * z) hprod

omit [Fintype L] in
theorem deletion_shortened_sublist
    (A : List L) (a : L) (C : List L) (b : L) (E : List L) :
    List.Sublist (A ++ C ++ E) (A ++ a :: C ++ b :: E) := by
  induction A with
  | nil =>
      simp only [List.nil_append]
      have hCE : List.Sublist (C ++ E) (C ++ b :: E) :=
        (List.Sublist.refl C).append
          ((List.Sublist.refl E).cons b)
      exact hCE.cons a
  | cons x A ih =>
      simpa only [List.cons_append] using ih.cons_cons x

/-- Repeated deletion produces a reduced sublist with unchanged product. -/
theorem exists_reduced_sublist_same_product
    (G : SimpleGraph L) (Q : List L) :
    ∃ R : List L, List.Sublist R Q ∧
      IsReduced G R ∧ wordProd G R = wordProd G Q := by
  induction hlen : Q.length using Nat.strong_induction_on generalizing Q with
  | h n ih =>
      by_cases hQ : IsReduced G Q
      · exact ⟨Q, List.Sublist.refl Q, hQ, rfl⟩
      · obtain ⟨A, a, C, b, E, hsplit, hprod⟩ :=
          hasDeletionCondition_simpleGraph G Q hQ
        let Q' := A ++ C ++ E
        have hlt : Q'.length < Q.length := by
          simp [Q', hsplit]
        obtain ⟨R, hRQ', hRred, hRprod⟩ :=
          ih Q'.length (by omega) Q' rfl
        refine ⟨R, hRQ'.trans ?_, hRred, hRprod.trans hprod.symm⟩
        subst Q
        exact deletion_shortened_sublist A a C b E

/-- A downward Bruhat step is left multiplication by a reflection with a
strict Coxeter-length drop. -/
def BruhatStep (G : SimpleGraph L) (u v : Group G) : Prop :=
  ∃ t : Group G,
    (system G).IsReflection t ∧ u = t * v ∧
      (system G).length u < (system G).length v

/-- Intrinsic strong Bruhat relation: the reflexive transitive closure of
reflection-length steps. -/
def BruhatLE (G : SimpleGraph L) : Group G → Group G → Prop :=
  Relation.ReflTransGen (BruhatStep G)

/-- A reduced expression for `u` occurring as a list subword of `Q`. -/
def HasReducedSubword
    (G : SimpleGraph L) (Q : List L) (u : Group G) : Prop :=
  ∃ R : List L, List.Sublist R Q ∧
    IsReduced G R ∧ wordProd G R = u

/-- One downward Bruhat step can be realized inside any chosen reduced
expression of its upper endpoint. -/
theorem hasReducedSubword_of_bruhatStep
    (G : SimpleGraph L) {u v : Group G}
    (huv : BruhatStep G u v)
    (Q : List L) (hQ : IsReduced G Q)
    (hQprod : wordProd G Q = v) :
    HasReducedSubword G Q u := by
  obtain ⟨t, ht, hut, hlen⟩ := huv
  have hdrop :
      (system G).length (t * wordProd G Q) <
        (system G).length (wordProd G Q) := by
    simpa [hQprod, hut] using hlen
  obtain ⟨k, hk, hdelete⟩ :=
    hasStrongLeftExchange_simpleGraph G Q hQ t ht hdrop
  obtain ⟨R, hRsub, hRred, hRprod⟩ :=
    exists_reduced_sublist_same_product G (Q.eraseIdx k)
  refine ⟨R, hRsub.trans (List.eraseIdx_sublist Q k), hRred, ?_⟩
  calc
    wordProd G R = wordProd G (Q.eraseIdx k) := hRprod
    _ = t * wordProd G Q := hdelete.symm
    _ = u := by rw [hQprod, hut]

/-- Every element below `wordProd Q` in intrinsic Bruhat order has a reduced
subword in the particular reduced expression `Q`.  This is the difficult
expression-independence direction of the subword theorem. -/
theorem hasReducedSubword_of_bruhatLE
    (G : SimpleGraph L) {u v : Group G}
    (huv : BruhatLE G u v)
    (Q : List L) (hQ : IsReduced G Q)
    (hQprod : wordProd G Q = v) :
    HasReducedSubword G Q u := by
  induction huv using Relation.ReflTransGen.head_induction_on with
  | refl =>
      exact ⟨Q, List.Sublist.refl Q, hQ, hQprod⟩
  | @head u c huc hcv ih =>
      obtain ⟨R, hRsub, hRred, hRprod⟩ := ih
      obtain ⟨S, hSsub, hSred, hSprod⟩ :=
        hasReducedSubword_of_bruhatStep G huc R hRred hRprod
      exact ⟨S, hSsub.trans hRsub, hSred, hSprod⟩

/-! ## Augmentation of a reduced subword -/

omit [Fintype L] in
theorem sort_univ_fin (n : ℕ) :
    (Finset.univ : Finset (Fin n)).sort
        (fun x y : Fin n ↦ x ≤ y) = List.finRange n := by
  simpa using
    ((List.toFinset_sort (fun x y : Fin n ↦ x ≤ y)
      (List.nodup_finRange n)).2
        ((List.sortedLT_finRange n).pairwise.imp fun h ↦ h.le))

omit [Fintype L] in
theorem sort_Iio_map_get_eq_take
    (Q : List L) (p : Fin Q.length) :
    ((Finset.Iio p).sort (fun x y : Fin Q.length ↦ x ≤ y)).map Q.get =
      Q.take p.val := by
  let f : Fin p.val → Fin Q.length := Fin.castLE p.isLt.le
  have hfmem : ∀ i, f i ∈ Finset.Iio p := by
    intro i
    exact Finset.mem_Iio.mpr i.isLt
  have hforder :
      f = (Finset.Iio p).orderEmbOfFin (Fin.card_Iio p) :=
    Finset.orderEmbOfFin_unique (Fin.card_Iio p) hfmem
      (Fin.strictMono_castLE p.isLt.le)
  have hsort :
      (List.finRange p.val).map f =
        (Finset.Iio p).sort (fun x y : Fin Q.length ↦ x ≤ y) := by
    rw [hforder]
    exact Finset.listMap_orderEmbOfFin_finRange
      (Finset.Iio p) (Fin.card_Iio p)
  rw [← hsort, List.map_map, ← List.ofFn_eq_map]
  exact Fin.ofFn_take_get Q p.isLt.le

omit [Fintype L] in
theorem filter_lt_sort_eq_sort_filter
    {n : ℕ} (D : Finset (Fin n)) (p : Fin n) :
    (D.sort (fun x y : Fin n ↦ x ≤ y)).filter (fun q ↦ q < p) =
      (D.filter fun q ↦ q < p).sort
        (fun x y : Fin n ↦ x ≤ y) := by
  apply (D.sortedLT_sort.pairwise.filter _).sortedLT.eq_of_mem_iff
    (D.filter fun q ↦ q < p).sortedLT_sort
  intro q
  simp

omit [Fintype L] in
/-- The first position missing from a proper support splits its sorted list
after the complete ambient prefix preceding that position. -/
theorem exists_first_gap_split
    (Q : List L) (D : Finset (Fin Q.length))
    (hD : D ≠ Finset.univ) :
    ∃ p : Fin Q.length, ∃ post : List (Fin Q.length),
      D.sort (fun x y : Fin Q.length ↦ x ≤ y) =
          (Finset.Iio p).sort (fun x y : Fin Q.length ↦ x ≤ y) ++ post ∧
        p ∉ D ∧
          (∀ q ∈ post, p < q) := by
  classical
  have hmissing : (Finset.univ \ D).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro hsubset
    apply hD
    exact Finset.eq_univ_iff_forall.mpr (fun q ↦ hsubset (Finset.mem_univ q))
  let p : Fin Q.length := (Finset.univ \ D).min' hmissing
  have hpMissing : p ∈ Finset.univ \ D :=
    Finset.min'_mem (Finset.univ \ D) hmissing
  have hpNot : p ∉ D := (Finset.mem_sdiff.mp hpMissing).2
  have hbefore : ∀ q : Fin Q.length, q < p → q ∈ D := by
    intro q hqp
    by_contra hqD
    have hqMissing : q ∈ Finset.univ \ D := by simp [hqD]
    have hpq : p ≤ q :=
      Finset.min'_le (Finset.univ \ D) q hqMissing
    exact (not_le_of_gt hqp) hpq
  obtain ⟨pre, post, hsplit, hpre, hpost⟩ :=
    exists_gap_split_of_not_mem_pairwise
      D.sortedLT_sort.pairwise p (by simpa using hpNot)
  have hfilterSet :
      D.filter (fun q ↦ q < p) = Finset.Iio p := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_Iio]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨hbefore q h, h⟩⟩
  have hfilterList :
      (D.sort (fun x y : Fin Q.length ↦ x ≤ y)).filter
          (fun q ↦ q < p) = pre := by
    rw [hsplit, List.filter_append]
    have hpreSelf : pre.filter (fun q ↦ q < p) = pre := by
      apply List.filter_eq_self.mpr
      intro q hq
      simpa only [decide_eq_true_eq] using hpre q hq
    have hpostNil : post.filter (fun q ↦ q < p) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro q hq
      simpa only [decide_eq_true_eq] using
        not_lt_of_ge (hpost q hq).le
    rw [hpreSelf, hpostNil, List.append_nil]
  have hpreEq :
      pre = (Finset.Iio p).sort
        (fun x y : Fin Q.length ↦ x ≤ y) := by
    rw [← hfilterList,
      filter_lt_sort_eq_sort_filter, hfilterSet]
  refine ⟨p, post, ?_, hpNot, hpost⟩
  simpa [hpreEq] using hsplit

/-- A proper fixed-word element has a one-length augmentation still
represented by a reduced subword of the same reduced ambient expression. -/
theorem exists_fixedWordElement_bruhatStep_length_add_one
    (G : SimpleGraph L) (Q : List L) (hQ : IsReduced G Q)
    (u : FixedWordElement (system G) Q)
    (huQ : u.1 ≠ wordProd G Q) :
    ∃ v : FixedWordElement (system G) Q,
      BruhatStep G u.1 v.1 ∧
        (system G).length v.1 = (system G).length u.1 + 1 := by
  classical
  let D : Finset (Fin Q.length) :=
    lexFirstPositions (system G) Q u
  have hDleft :
      IsLeftmostReducedSubwordFor (system G) Q u.1 D :=
    lexFirstPositions_spec (system G) Q u
  have hDnotUniv : D ≠ Finset.univ := by
    intro hD
    apply huQ
    have hword : subwordAt Q D = Q := by
      rw [hD]
      rw [subwordAt, sort_univ_fin, List.map_get_finRange]
    exact (hword ▸ hDleft.1.2).symm
  obtain ⟨p, post, hDsplit, hpNot, hpost⟩ :=
    exists_first_gap_split Q D hDnotUniv
  let pre : List (Fin Q.length) :=
    (Finset.Iio p).sort (fun x y : Fin Q.length ↦ x ≤ y)
  let B : List L := pre.map Q.get
  let C : List L := post.map Q.get
  let a : L := Q.get p
  let R : List L := subwordAt Q D
  let Eidx : List (Fin Q.length) := pre ++ p :: post
  let Eword : List L := B ++ a :: C
  have hprePair : pre.Pairwise (fun x y ↦ x < y) := by
    exact (Finset.Iio p).sortedLT_sort.pairwise
  have hDpair :
      (D.sort (fun x y : Fin Q.length ↦ x ≤ y)).Pairwise
        (fun x y ↦ x < y) := D.sortedLT_sort.pairwise
  have hpostPair : post.Pairwise (fun x y ↦ x < y) := by
    rw [hDsplit] at hDpair
    exact (List.pairwise_append.mp hDpair).2.1
  have hEpair : Eidx.Pairwise (fun x y ↦ x < y) := by
    apply List.pairwise_append.mpr
    refine ⟨hprePair, ?_, ?_⟩
    · rw [List.pairwise_cons]
      exact ⟨hpost, hpostPair⟩
    · intro x hx y hy
      have hxp : x < p := by
        simpa [pre] using
          (Finset.mem_Iio.mp
            ((Finset.mem_sort
              (r := fun x y : Fin Q.length ↦ x ≤ y)).mp hx))
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact hxp
      · exact hxp.trans (hpost y hy)
  have hEsort :
      Eidx.toFinset.sort (fun x y : Fin Q.length ↦ x ≤ y) = Eidx := by
    exact (List.toFinset_sort
      (fun x y : Fin Q.length ↦ x ≤ y) hEpair.nodup).2
        (hEpair.imp fun h ↦ h.le)
  have hRsplit : R = B ++ C := by
    simp only [R, subwordAt, hDsplit, List.map_append, B, C, pre]
  have hBtake : B = Q.take p.val := by
    exact sort_Iio_map_get_eq_take Q p
  have hprefixRed : IsReduced G (B ++ [a]) := by
    change (system G).IsReduced (B ++ [a])
    have hpref := hQ.take (p.val + 1)
    rw [← List.take_concat_get (l := Q) (i := p.val) p.isLt] at hpref
    simpa only [SimpleGraphCoxeter.IsReduced, List.concat_eq_append,
      hBtake, a, List.get_eq_getElem] using hpref
  have hDred : IsReduced G R := hDleft.1.1
  have hDprod : wordProd G R = u.1 := hDleft.1.2
  have hEsubword :
      subwordAt Q Eidx.toFinset = Eword := by
    simp only [subwordAt, hEsort, Eidx, List.map_append,
      List.map_cons, B, C, a, Eword]
  let t : Group G :=
    wordProd G B * (system G).simple a * (wordProd G B)⁻¹
  have ht : (system G).IsReflection t := by
    exact ((system G).isReflection_simple a).conj (wordProd G B)
  have htu : t * u.1 = wordProd G Eword := by
    rw [← hDprod, hRsplit]
    simp only [t, Eword, SimpleGraphCoxeter.wordProd,
      CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_cons]
    group
  have hElen :
      Eword.length = R.length + 1 := by
    simp only [Eword, List.length_append, List.length_cons,
      hRsplit, B, C, List.length_map]
    omega

  have hEred : IsReduced G Eword := by
    by_contra hnotRed
    have hvLtSucc :
        (system G).length (wordProd G Eword) < R.length + 1 := by
      have hvLe := (system G).length_wordProd_le Eword
      rw [← hElen]
      exact lt_of_le_of_ne hvLe (by
        intro heq
        apply hnotRed
        exact heq)
    have huLen : (system G).length u.1 = R.length := by
      rw [← hDprod]
      exact hDred.eq
    have hvNe :
        (system G).length (wordProd G Eword) ≠
          (system G).length u.1 := by
      rw [← htu]
      exact ht.length_mul_right_ne u.1
    have hvDrop :
        (system G).length (t * wordProd G R) <
          (system G).length (wordProd G R) := by
      rw [hDprod, htu]
      omega
    obtain ⟨k, hk, hdelete⟩ :=
      hasStrongLeftExchange_simpleGraph G R hDred t ht hvDrop
    have hdelEq :
        wordProd G Eword = wordProd G ((B ++ C).eraseIdx k) := by
      calc
        wordProd G Eword = t * u.1 := htu.symm
        _ = t * wordProd G R := by rw [hDprod]
        _ = wordProd G (R.eraseIdx k) := hdelete
        _ = wordProd G ((B ++ C).eraseIdx k) := by rw [hRsplit]
    by_cases hkB : k < B.length
    · have hdelSplit :
          (B ++ C).eraseIdx k = B.eraseIdx k ++ C := by
        rw [List.eraseIdx_append, if_pos hkB]
      have hprefixProd :
          wordProd G (B ++ [a]) = wordProd G (B.eraseIdx k) := by
        apply mul_right_cancel (b := wordProd G C)
        simpa [Eword, hdelSplit, SimpleGraphCoxeter.wordProd,
          CoxeterSystem.wordProd_append,
          CoxeterSystem.wordProd_cons, mul_assoc] using hdelEq
      have hshort :
          (system G).length (wordProd G (B.eraseIdx k)) ≤
            (B.eraseIdx k).length := by
        simpa only [SimpleGraphCoxeter.wordProd] using
          (system G).length_wordProd_le (B.eraseIdx k)
      have hprefixLen :
          (system G).length (wordProd G (B ++ [a])) =
            (B ++ [a]).length := by
        simpa only [SimpleGraphCoxeter.wordProd] using hprefixRed.eq
      rw [hprefixProd] at hprefixLen
      have herase := List.length_eraseIdx_add_one hkB
      simp only [List.length_append, List.length_singleton] at hprefixLen
      omega
    · let j : ℕ := k - B.length
      have hjC : j < C.length := by
        have hk' : k < B.length + C.length := by
          simpa [hRsplit] using hk
        simp only [j]
        omega
      have hjPost : j < post.length := by
        simpa [C] using hjC
      have hdelSplit :
          (B ++ C).eraseIdx k = B ++ C.eraseIdx j := by
        rw [List.eraseIdx_append, if_neg hkB]
      have htailProd :
          (system G).simple a * wordProd G C =
            wordProd G (C.eraseIdx j) := by
        apply mul_left_cancel (a := wordProd G B)
        simpa [Eword, hdelSplit, SimpleGraphCoxeter.wordProd,
          CoxeterSystem.wordProd_append,
          CoxeterSystem.wordProd_cons, mul_assoc] using hdelEq
      have htailSwap :
          wordProd G C =
            (system G).simple a * wordProd G (C.eraseIdx j) := by
        calc
          wordProd G C =
              (system G).simple a *
                ((system G).simple a * wordProd G C) := by
            rw [(system G).simple_mul_simple_cancel_left]
          _ = (system G).simple a *
              wordProd G (C.eraseIdx j) := by rw [htailProd]
      let Aidx : List (Fin Q.length) :=
        pre ++ p :: post.eraseIdx j
      have hpostEraseSub : List.Sublist (post.eraseIdx j) post :=
        List.eraseIdx_sublist post j
      have hpostErasePair :
          (post.eraseIdx j).Pairwise (fun x y ↦ x < y) :=
        List.Pairwise.sublist hpostEraseSub hpostPair
      have hApair : Aidx.Pairwise (fun x y ↦ x < y) := by
        apply List.pairwise_append.mpr
        refine ⟨hprePair, ?_, ?_⟩
        · rw [List.pairwise_cons]
          refine ⟨?_, hpostErasePair⟩
          intro q hq
          exact hpost q (hpostEraseSub.mem hq)
        · intro x hx y hy
          have hxp : x < p := by
            simpa [pre] using
              (Finset.mem_Iio.mp
                ((Finset.mem_sort
                  (r := fun x y : Fin Q.length ↦ x ≤ y)).mp hx))
          simp only [List.mem_cons] at hy
          rcases hy with rfl | hy
          · exact hxp
          · exact hxp.trans
              (hpost y (hpostEraseSub.mem hy))
      have hAsort :
          Aidx.toFinset.sort
              (fun x y : Fin Q.length ↦ x ≤ y) = Aidx := by
        exact (List.toFinset_sort
          (fun x y : Fin Q.length ↦ x ≤ y) hApair.nodup).2
            (hApair.imp fun h ↦ h.le)
      have hAsubword :
          subwordAt Q Aidx.toFinset =
            B ++ a :: C.eraseIdx j := by
        simp only [subwordAt, hAsort, Aidx, List.map_append,
          List.map_cons, B, C, a, List.eraseIdx_map]
      have hAprod :
          wordProd G (subwordAt Q Aidx.toFinset) = u.1 := by
        rw [hAsubword]
        calc
          wordProd G (B ++ a :: C.eraseIdx j) =
              wordProd G B *
                ((system G).simple a *
                  wordProd G (C.eraseIdx j)) := by
            simp [SimpleGraphCoxeter.wordProd,
              CoxeterSystem.wordProd_append,
              CoxeterSystem.wordProd_cons]
          _ = wordProd G B * wordProd G C := by rw [← htailSwap]
          _ = wordProd G (B ++ C) := by
            simpa only [SimpleGraphCoxeter.wordProd] using
              ((system G).wordProd_append B C).symm
          _ = wordProd G R := by rw [hRsplit]
          _ = u.1 := hDprod
      have hAlength :
          (subwordAt Q Aidx.toFinset).length = R.length := by
        rw [hAsubword, hRsplit]
        have herase := List.length_eraseIdx_add_one hjC
        simp only [List.length_append, List.length_cons]
        omega
      have hAred :
          IsReduced G (subwordAt Q Aidx.toFinset) := by
        unfold SimpleGraphCoxeter.IsReduced CoxeterSystem.IsReduced
        change (system G).length
          (wordProd G (subwordAt Q Aidx.toFinset)) = _
        rw [hAprod, huLen, hAlength]
      have hAcandidate :
          IsReducedSubwordFor (system G) Q u.1 Aidx.toFinset :=
        ⟨hAred, hAprod⟩
      have hpostNe : post ≠ [] := by
        intro hpostNil
        simp [hpostNil] at hjPost
      obtain ⟨q, postTail, rfl⟩ := List.exists_cons_of_ne_nil hpostNe
      have hpq : p < q := hpost q (by simp)
      have hlexTail :
          List.Lex (fun x y : Fin Q.length ↦ x < y)
            (p :: (q :: postTail).eraseIdx j) (q :: postTail) :=
        List.Lex.rel hpq
      have hlex :
          List.Lex (fun x y : Fin Q.length ↦ x < y)
            (Aidx.toFinset.sort
              (fun x y : Fin Q.length ↦ x ≤ y))
            (D.sort (fun x y : Fin Q.length ↦ x ≤ y)) := by
        rw [hAsort, hDsplit]
        exact List.Lex.append_left
          (fun x y : Fin Q.length ↦ x < y) hlexTail pre
      exact hDleft.2 Aidx.toFinset hAcandidate hlex
  have hEredSubword :
      (system G).IsReduced (subwordAt Q Eidx.toFinset) := by
    rw [hEsubword]
    exact hEred
  have hEprodSubword :
      (system G).wordProd (subwordAt Q Eidx.toFinset) =
        wordProd G Eword := by
    rw [hEsubword]
    rfl
  let v : FixedWordElement (system G) Q :=
    ⟨wordProd G Eword,
      Eidx.toFinset, hEredSubword, hEprodSubword⟩
  refine ⟨v, ?_, ?_⟩
  · refine ⟨t, ht, ?_, ?_⟩
    · change u.1 = t * wordProd G Eword
      rw [← htu, ← mul_assoc, ht.mul_self, one_mul]
    · change (system G).length u.1 <
        (system G).length (wordProd G Eword)
      have hvLen :
          (system G).length (wordProd G Eword) = Eword.length := by
        simpa only [SimpleGraphCoxeter.wordProd] using hEred.eq
      have huLen : (system G).length u.1 = R.length := by
        rw [← hDprod]
        exact hDred.eq
      omega
  · change (system G).length (wordProd G Eword) =
      (system G).length u.1 + 1
    have hvLen :
        (system G).length (wordProd G Eword) = Eword.length := by
      simpa only [SimpleGraphCoxeter.wordProd] using hEred.eq
    have huLen : (system G).length u.1 = R.length := by
      rw [← hDprod]
      exact hDred.eq
    omega

omit [Fintype L] in
@[simp]
theorem subwordAt_univ (Q : List L) :
    subwordAt Q (Finset.univ : Finset (Fin Q.length)) = Q := by
  rw [subwordAt, sort_univ_fin, List.map_get_finRange]

omit [Fintype L] in
/-- A fixed-word element cannot have length exceeding the ambient word. -/
theorem length_fixedWordElement_le
    (G : SimpleGraph L) (Q : List L)
    (u : FixedWordElement (system G) Q) :
    (system G).length u.1 ≤ Q.length := by
  obtain ⟨D, hDred, hDprod⟩ := u.2
  calc
    (system G).length u.1 =
        (system G).length
          ((system G).wordProd (subwordAt Q D)) := by rw [hDprod]
    _ = (subwordAt Q D).length := hDred.eq
    _ = D.card := length_subwordAt Q D
    _ ≤ Q.length := by
      simpa using Finset.card_le_univ D

omit [Fintype L] in
/-- In a reduced ambient expression, a fixed-word element of full ambient
length is the ambient product itself. -/
theorem fixedWordElement_eq_wordProd_of_length_eq
    (G : SimpleGraph L) (Q : List L)
    (u : FixedWordElement (system G) Q)
    (hlen : (system G).length u.1 = Q.length) :
    u.1 = wordProd G Q := by
  obtain ⟨D, hDred, hDprod⟩ := u.2
  have hcard : D.card = Q.length := by
    calc
      D.card = (subwordAt Q D).length :=
        (length_subwordAt Q D).symm
      _ = (system G).length
          ((system G).wordProd (subwordAt Q D)) := hDred.eq.symm
      _ = (system G).length u.1 := by rw [hDprod]
      _ = Q.length := hlen
  have hDuniv : D = Finset.univ := by
    apply Finset.eq_univ_of_card
    simpa using hcard
  calc
    u.1 = (system G).wordProd (subwordAt Q D) := hDprod.symm
    _ = (system G).wordProd Q := by rw [hDuniv, subwordAt_univ]
    _ = wordProd G Q := rfl

/-- Repeated one-length augmentation reaches the ambient product. -/
theorem bruhatLE_of_fixedWordElement
    (G : SimpleGraph L) (Q : List L) (hQ : IsReduced G Q)
    (u : FixedWordElement (system G) Q) :
    BruhatLE G u.1 (wordProd G Q) := by
  induction hgap : Q.length - (system G).length u.1 using
      Nat.strong_induction_on generalizing u with
  | h n ih =>
      by_cases huQ : u.1 = wordProd G Q
      · rw [huQ]
        exact Relation.ReflTransGen.refl
      · obtain ⟨v, huv, hvlen⟩ :=
          exists_fixedWordElement_bruhatStep_length_add_one
            G Q hQ u huQ
        have hulenLe := length_fixedWordElement_le G Q u
        have hulenLt : (system G).length u.1 < Q.length := by
          apply lt_of_le_of_ne hulenLe
          intro heq
          exact huQ
            (fixedWordElement_eq_wordProd_of_length_eq
              G Q u heq)
        have hmeasure :
            Q.length - (system G).length v.1 <
              Q.length - (system G).length u.1 := by
          omega
        have hvQ : BruhatLE G v.1 (wordProd G Q) :=
          ih (Q.length - (system G).length v.1)
            (by simpa [hgap] using hmeasure) v rfl
        exact Relation.ReflTransGen.head huv hvQ

omit [Fintype L] in
/-- Every list subword is selected by a finite set of ambient positions. -/
theorem exists_positions_of_sublist
    {R Q : List L} (hRQ : List.Sublist R Q) :
    ∃ D : Finset (Fin Q.length), subwordAt Q D = R := by
  classical
  obtain ⟨f, hf⟩ :=
    (List.sublist_iff_exists_fin_orderEmbedding_get_eq).mp hRQ
  let D : Finset (Fin Q.length) :=
    Finset.univ.map f.toEmbedding
  have hsort :
      D.sort (fun x y : Fin Q.length ↦ x ≤ y) =
        (List.finRange R.length).map f := by
    have hmapSort := Finset.map_sort f.toEmbedding
      (Finset.univ : Finset (Fin R.length))
      (fun x y : Fin R.length ↦ x ≤ y)
      (fun x y : Fin Q.length ↦ x ≤ y)
      (by
        intro x _ y _
        exact f.le_iff_le.symm)
    rw [sort_univ_fin] at hmapSort
    exact hmapSort.symm
  refine ⟨D, ?_⟩
  rw [subwordAt, hsort, List.map_map]
  calc
    (List.finRange R.length).map (Q.get ∘ f) =
        (List.finRange R.length).map R.get := by
      apply List.map_congr_left
      intro i hi
      exact (hf i).symm
    _ = R := List.map_get_finRange R

omit [Fintype L] in
/-- List-subword witnesses and the finite-position fixed-word interface
describe the same elements. -/
theorem fixedWordElement_of_hasReducedSubword
    (G : SimpleGraph L) (Q : List L) (u : Group G)
    (hu : HasReducedSubword G Q u) :
    ∃ v : FixedWordElement (system G) Q, v.1 = u := by
  obtain ⟨R, hRQ, hRred, hRprod⟩ := hu
  obtain ⟨D, hD⟩ := exists_positions_of_sublist hRQ
  let v : FixedWordElement (system G) Q :=
    ⟨u, D, by
        rw [hD]
        simpa only [SimpleGraphCoxeter.IsReduced] using hRred,
      by
        rw [hD]
        simpa only [SimpleGraphCoxeter.wordProd] using hRprod⟩
  exact ⟨v, rfl⟩

/-- The converse direction of the Bruhat subword theorem. -/
theorem bruhatLE_of_hasReducedSubword
    (G : SimpleGraph L) (Q : List L) (hQ : IsReduced G Q)
    (u : Group G) (hu : HasReducedSubword G Q u) :
    BruhatLE G u (wordProd G Q) := by
  obtain ⟨v, rfl⟩ := fixedWordElement_of_hasReducedSubword G Q u hu
  exact bruhatLE_of_fixedWordElement G Q hQ v

/-- Full intrinsic Bruhat/subword theorem for the graph Coxeter system. -/
theorem bruhatLE_iff_hasReducedSubword
    (G : SimpleGraph L) (Q : List L) (hQ : IsReduced G Q)
    (u : Group G) :
    BruhatLE G u (wordProd G Q) ↔ HasReducedSubword G Q u := by
  constructor
  · intro hu
    exact hasReducedSubword_of_bruhatLE G hu Q hQ rfl
  · exact bruhatLE_of_hasReducedSubword G Q hQ u

/-- Finite-position form of the intrinsic Bruhat subword theorem. -/
theorem bruhatLE_iff_exists_reducedSubwordFor
    (G : SimpleGraph L) (Q : List L) (hQ : IsReduced G Q)
    (u : Group G) :
    BruhatLE G u (wordProd G Q) ↔
      ∃ D : Finset (Fin Q.length),
        IsReducedSubwordFor (system G) Q u D := by
  constructor
  · intro hu
    obtain ⟨R, hRQ, hRred, hRprod⟩ :=
      hasReducedSubword_of_bruhatLE G hu Q hQ rfl
    obtain ⟨D, hD⟩ := exists_positions_of_sublist hRQ
    refine ⟨D, ?_, ?_⟩
    · rw [hD]
      simpa only [SimpleGraphCoxeter.IsReduced] using hRred
    · rw [hD]
      simpa only [SimpleGraphCoxeter.wordProd] using hRprod
  · rintro ⟨D, hD⟩
    let v : FixedWordElement (system G) Q := ⟨u, D, hD⟩
    exact bruhatLE_of_fixedWordElement G Q hQ v

/-- The principal intrinsic Bruhat interval below the product of `Q`. -/
def BruhatLowerInterval (G : SimpleGraph L) (Q : List L) :=
  {u : Group G // BruhatLE G u (wordProd G Q)}

/-- For a reduced ambient expression, its fixed-word elements are exactly
the intrinsic principal Bruhat interval below its product. -/
def fixedWordElementEquivBruhatLowerInterval
    (G : SimpleGraph L) (Q : List L) (hQ : IsReduced G Q) :
    FixedWordElement (system G) Q ≃ BruhatLowerInterval G Q where
  toFun u := ⟨u.1, bruhatLE_of_fixedWordElement G Q hQ u⟩
  invFun u :=
    ⟨u.1, (bruhatLE_iff_exists_reducedSubwordFor
      G Q hQ u.1).mp u.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The lexicographically first reduced position set of an element in the
principal Bruhat interval. -/
def bruhatLexFirstPositions
    (G : SimpleGraph L) (Q : List L) (hQ : IsReduced G Q)
    (u : BruhatLowerInterval G Q) : Finset (Fin Q.length) :=
  (lexFirstLocalPositions G Q
    ((fixedWordElementEquivBruhatLowerInterval G Q hQ).symm u)).1

/-- The lex-first Bruhat support has cardinality equal to Coxeter length. -/
theorem card_bruhatLexFirstPositions
    (G : SimpleGraph L) (Q : List L) (hQ : IsReduced G Q)
    (u : BruhatLowerInterval G Q) :
    (bruhatLexFirstPositions G Q hQ u).card =
      (system G).length u.1 := by
  exact card_lexFirstLocalPositions G Q
    ((fixedWordElementEquivBruhatLowerInterval G Q hQ).symm u)

/-- The finite structure on a principal interval transported across the
proved subword equivalence. -/
@[reducible] noncomputable def bruhatLowerIntervalFintype
    (G : SimpleGraph L) (Q : List L) (hQ : IsReduced G Q) :
    Fintype (BruhatLowerInterval G Q) :=
  Fintype.ofEquiv (FixedWordElement (system G) Q)
    (fixedWordElementEquivBruhatLowerInterval G Q hQ)

/-- Reverse Coxeter-length polynomial of the principal intrinsic Bruhat
interval, using the finite structure supplied by the subword theorem. -/
noncomputable def bruhatLowerIntervalReverseLengthPolynomial
    (G : SimpleGraph L) (Q : List L) (hQ : IsReduced G Q) : ℕ[X] := by
  letI := bruhatLowerIntervalFintype G Q hQ
  exact ∑ u : BruhatLowerInterval G Q,
    X ^ (Q.length - (system G).length u.1)

/-- Exact fixed-word profile theorem: locally reduced supports enumerate the
principal intrinsic Bruhat interval by reverse Coxeter length. -/
theorem locallyReducedPositions_generatingFunction_eq_bruhatLowerInterval
    (G : SimpleGraph L) (Q : List L) (hQ : IsReduced G Q) :
    (∑ D : LocallyReducedPositions G Q,
        X ^ (Q.length - D.1.card) : ℕ[X]) =
      bruhatLowerIntervalReverseLengthPolynomial G Q hQ := by
  rw [locallyReducedPositions_generatingFunction]
  let e := fixedWordElementEquivBruhatLowerInterval G Q hQ
  letI := bruhatLowerIntervalFintype G Q hQ
  unfold bruhatLowerIntervalReverseLengthPolynomial
  calc
    (∑ u : FixedWordElement (system G) Q,
        X ^ (Q.length - (system G).length u.1) : ℕ[X]) =
        ∑ u : FixedWordElement (system G) Q,
          X ^ (Q.length - (system G).length (e u).1) := by
      apply Finset.sum_congr rfl
      intro u _
      rfl
    _ = ∑ u : BruhatLowerInterval G Q,
        X ^ (Q.length - (system G).length u.1) :=
      e.sum_comp
        (fun u : BruhatLowerInterval G Q ↦
          (X ^ (Q.length - (system G).length u.1) : ℕ[X]))

end QuotientSubmoduleEquidistribution.RepresentationDirected.SimpleGraphBruhat
