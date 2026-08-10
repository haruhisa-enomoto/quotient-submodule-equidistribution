import QuotientSubmoduleEquidistribution.RepresentationDirected.FixedWordSubwords
import QuotientSubmoduleEquidistribution.RepresentationDirected.ARCoordinateRecurrence
import QuotientSubmoduleEquidistribution.RepresentationDirected.SimpleGraphTitsForm

/-!
# Simple exchange and fixed-word sorting

This file proves simple exchange for the Coxeter system of an arbitrary
finite simple graph and the fixed-word local recognition criterion used in
the representation-directed sorting argument.
-/

set_option autoImplicit false

noncomputable section

namespace QuotientSubmoduleEquidistribution.RepresentationDirected.SortingExchange

open QuotientSubmoduleEquidistribution.RepresentationDirected.FixedWord
open FixedWordSubwords

universe uB uW

variable {B : Type uB} {W : Type uW}
variable [Group W] {M : CoxeterMatrix B}
variable (cs : CoxeterSystem M W)

/-- The simple left-exchange statement in factorization form. -/
def HasSimpleLeftExchange : Prop :=
  ∀ (Q : List B) (i : B),
    cs.IsReduced Q →
      cs.IsLeftDescent (cs.wordProd Q) i →
        ∃ pre x post,
          Q = pre ++ x :: post ∧
            cs.simple i * cs.wordProd Q =
              cs.wordProd (pre ++ post)

/-- The right-handed companion of `HasSimpleLeftExchange`. -/
def HasSimpleRightExchange : Prop :=
  ∀ (Q : List B) (i : B),
    cs.IsReduced Q →
      cs.IsRightDescent (cs.wordProd Q) i →
        ∃ pre x post,
          Q = pre ++ x :: post ∧
            cs.wordProd Q * cs.simple i =
              cs.wordProd (pre ++ post)

/-- Reversal turns simple right exchange into simple left exchange. -/
theorem hasSimpleLeftExchange_of_hasSimpleRightExchange
    (hRight : HasSimpleRightExchange cs) :
    HasSimpleLeftExchange cs := by
  intro Q i hQ hleft
  have hQrev : cs.IsReduced Q.reverse := hQ.reverse
  have hright :
      cs.IsRightDescent (cs.wordProd Q.reverse) i := by
    rw [cs.wordProd_reverse]
    exact cs.isRightDescent_inv_iff.mpr hleft
  obtain ⟨pre, x, post, hsplit, hprod⟩ :=
    hRight Q.reverse i hQrev hright
  refine ⟨post.reverse, x, pre.reverse, ?_, ?_⟩
  · have := congrArg List.reverse hsplit
    simpa [List.reverse_append] using this
  · have hinv := congrArg Inv.inv hprod
    calc
      cs.simple i * cs.wordProd Q =
          (cs.wordProd (pre ++ post))⁻¹ := by
        simpa [cs.wordProd_reverse] using hinv
      _ = cs.wordProd (pre ++ post).reverse :=
        (cs.wordProd_reverse (pre ++ post)).symm
      _ = cs.wordProd (post.reverse ++ pre.reverse) := by
        rw [List.reverse_append]

/-- Prefixing a reduced word by a simple generator is reduced exactly when
that generator is not a left descent of the represented element. -/
theorem isReduced_cons_iff_not_isLeftDescent
    (Q : List B) (i : B) (hQ : cs.IsReduced Q) :
    cs.IsReduced (i :: Q) ↔
      ¬ cs.IsLeftDescent (cs.wordProd Q) i := by
  rw [CoxeterSystem.IsReduced, CoxeterSystem.wordProd_cons,
    cs.not_isLeftDescent_iff, hQ.eq]
  simp

/-! ## Strictly increasing index-list form of fixed-word sorting -/

/-- A strictly increasing index list selecting a reduced expression for
`w` from an indexed ambient word. -/
def IsReducedIndexListFor {n : ℕ}
    (word : Fin n → B) (w : W) (D : List (Fin n)) : Prop :=
  D.Pairwise (· < ·) ∧
    cs.IsReduced (D.map word) ∧
      cs.wordProd (D.map word) = w

/-- Lexicographic minimality among strictly increasing reduced index lists. -/
def IsLeftmostReducedIndexListFor {n : ℕ}
    (word : Fin n → B) (w : W) (D : List (Fin n)) : Prop :=
  IsReducedIndexListFor cs word w D ∧
    ∀ E : List (Fin n),
      IsReducedIndexListFor cs word w E →
        ¬ List.Lex (· < ·) E D

/-- The list form of the manuscript's local `D[a]` criterion. -/
def AreAllLocalIndexSubwordsReduced {n : ℕ}
    (word : Fin n → B) (D : List (Fin n)) : Prop :=
  ∀ a : Fin n,
    cs.IsReduced
      (word a :: (D.filter fun d ↦ a < d).map word)

/-- Equal-length lexicographically related lists have a common prefix and a
first strict inequality. -/
theorem exists_first_difference_of_lex_of_length_eq
    {n : ℕ} {E D : List (Fin n)}
    (hlex : List.Lex (· < ·) E D)
    (hlen : E.length = D.length) :
    ∃ P a E' d D',
      E = P ++ a :: E' ∧ D = P ++ d :: D' ∧ a < d := by
  induction hlex with
  | nil => simp at hlen
  | @rel a E b D hab =>
      exact ⟨[], a, E, b, D, rfl, rfl, hab⟩
  | @cons a E D _ ih =>
      have htail : E.length = D.length := by simpa using hlen
      obtain ⟨P, b, E', d, D', hE, hD, hbd⟩ := ih htail
      exact ⟨a :: P, b, E', d, D', by simp [hE], by simp [hD], hbd⟩

/-- If a member occurs in a strictly increasing list, filtering for entries
strictly after it gives precisely the tail after that occurrence. -/
theorem exists_split_filter_gt_of_mem_pairwise
    {n : ℕ} {D : List (Fin n)} (hD : D.Pairwise (· < ·))
    {a : Fin n} (ha : a ∈ D) :
    ∃ pre post, D = pre ++ a :: post ∧
      D.filter (fun d ↦ a < d) = post := by
  induction D with
  | nil => simp at ha
  | cons b D ih =>
      rw [List.pairwise_cons] at hD
      simp only [List.mem_cons] at ha
      rcases ha with hab | ha
      · subst b
        refine ⟨[], D, rfl, ?_⟩
        have hfilter : D.filter (fun d ↦ a < d) = D := by
          rw [List.filter_eq_self]
          intro d hd
          simp [hD.1 d hd]
        simp [hfilter]
      · obtain ⟨pre, post, hsplit, hfilter⟩ := ih hD.2 ha
        refine ⟨b :: pre, post, by simp [hsplit], ?_⟩
        have hba : b < a := hD.1 a ha
        have hab : ¬ a < b := not_lt_of_ge hba.le
        simp [hab, hfilter]

/-- A point outside a strictly increasing list determines a unique gap; this
existence form supplies the prefix and suffix needed by exchange. -/
theorem exists_gap_split_of_not_mem_pairwise
    {n : ℕ} {D : List (Fin n)} (hD : D.Pairwise (· < ·))
    (a : Fin n) (ha : a ∉ D) :
    ∃ pre post,
      D = pre ++ post ∧
        (∀ p ∈ pre, p < a) ∧
          (∀ p ∈ post, a < p) := by
  induction D with
  | nil => exact ⟨[], [], rfl, by simp, by simp⟩
  | cons b D ih =>
      rw [List.pairwise_cons] at hD
      simp only [List.mem_cons, not_or] at ha
      by_cases hba : b < a
      · obtain ⟨pre, post, hsplit, hpre, hpost⟩ :=
          ih hD.2 ha.2
        refine ⟨b :: pre, post, by simp [hsplit], ?_, hpost⟩
        intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with hpb | hp
        · simpa [hpb] using hba
        · exact hpre p hp
      · have hab : a < b := lt_of_le_of_ne (le_of_not_gt hba) ha.1
        refine ⟨[], b :: D, by simp, by simp, ?_⟩
        intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with hpb | hp
        · simpa [hpb] using hab
        · exact hab.trans (hD.1 p hp)

/-- At the first differing entry of two strictly increasing lists, filtering
the second list for positions after the smaller entry returns its entire
remaining suffix. -/
theorem filter_gt_eq_suffix_at_first_difference
    {n : ℕ} {P E' D' : List (Fin n)} {a d : Fin n}
    (hE : (P ++ a :: E').Pairwise (· < ·))
    (hD : (P ++ d :: D').Pairwise (· < ·))
    (had : a < d) :
    (P ++ d :: D').filter (fun x ↦ a < x) = d :: D' := by
  have hEappend := List.pairwise_append.mp hE
  have hDappend := List.pairwise_append.mp hD
  have hprefix : P.filter (fun x ↦ a < x) = [] := by
    rw [List.filter_eq_nil_iff]
    intro p hp
    have hpa : p < a := hEappend.2.2 p hp a (by simp)
    simp [not_lt_of_ge hpa.le]
  have htailAll : ∀ x ∈ d :: D', a < x := by
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with hxd | hx
    · simpa [hxd] using had
    · have hdx : d < x :=
        (List.pairwise_cons.mp hDappend.2.1).1 x hx
      exact had.trans hdx
  have htail : (d :: D').filter (fun x ↦ a < x) = d :: D' := by
    rw [List.filter_eq_self]
    intro x hx
    simp [htailAll x hx]
  simp [List.filter_append, hprefix, htail]

/-- Index form of simple left exchange. -/
theorem exists_eraseIdx_of_simpleLeftExchange
    (hExchange : HasSimpleLeftExchange cs)
    (Q : List B) (i : B) (hQ : cs.IsReduced Q)
    (hdescent : cs.IsLeftDescent (cs.wordProd Q) i) :
    ∃ k, k < Q.length ∧
      cs.simple i * cs.wordProd Q = cs.wordProd (Q.eraseIdx k) := by
  obtain ⟨pre, x, post, hsplit, hprod⟩ :=
    hExchange Q i hQ hdescent
  refine ⟨pre.length, ?_, ?_⟩
  · simp [hsplit]
  · rw [hsplit, List.eraseIdx_eq_take_drop_succ]
    have hprod' := hprod
    rw [hsplit] at hprod'
    simpa using hprod'

/-- The exchange implication in the fixed-word recognition criterion:
lexicographically first reduced index lists have every local `D[a]` word
reduced. -/
theorem allLocal_of_leftmost_of_simpleLeftExchange
    {n : ℕ} (word : Fin n → B) (w : W) (D : List (Fin n))
    (hExchange : HasSimpleLeftExchange cs)
    (hleftmost : IsLeftmostReducedIndexListFor cs word w D) :
    AreAllLocalIndexSubwordsReduced cs word D := by
  intro a
  rcases hleftmost.1 with ⟨hDpair, hDred, hDprod⟩
  by_cases ha : a ∈ D
  · obtain ⟨pre, post, hsplit, hfilter⟩ :=
      exists_split_filter_gt_of_mem_pairwise hDpair ha
    rw [hfilter]
    have hdrop := hDred.drop pre.length
    simpa [hsplit] using hdrop
  · obtain ⟨pre, post, hsplit, hpre, hpost⟩ :=
      exists_gap_split_of_not_mem_pairwise hDpair a ha
    have hfilter : D.filter (fun d ↦ a < d) = post := by
      rw [hsplit, List.filter_append]
      have hpreFilter : pre.filter (fun d ↦ a < d) = [] := by
        rw [List.filter_eq_nil_iff]
        intro p hp
        simp [not_lt_of_ge (hpre p hp).le]
      have hpostFilter : post.filter (fun d ↦ a < d) = post := by
        rw [List.filter_eq_self]
        intro p hp
        simp [hpost p hp]
      simp [hpreFilter, hpostFilter]
    rw [hfilter]
    have hpostRed : cs.IsReduced (post.map word) := by
      have hdrop := hDred.drop pre.length
      simpa [hsplit] using hdrop
    by_contra hlocal
    have hdescent :
        cs.IsLeftDescent (cs.wordProd (post.map word)) (word a) :=
      not_not.mp
        ((isReduced_cons_iff_not_isLeftDescent cs
          (post.map word) (word a) hpostRed).not.mp hlocal)
    obtain ⟨k, hk, hexchange⟩ :=
      exists_eraseIdx_of_simpleLeftExchange cs hExchange
        (post.map word) (word a) hpostRed hdescent
    have hkPost : k < post.length := by simpa using hk
    let post' : List (Fin n) := post.eraseIdx k
    let E : List (Fin n) := pre ++ a :: post'
    have hpostPair : post.Pairwise (· < ·) := by
      have hsplitPair : (pre ++ post).Pairwise (· < ·) := by
        simpa [hsplit] using hDpair
      exact (List.pairwise_append.mp hsplitPair).2.1
    have hprePair : pre.Pairwise (· < ·) := by
      have hsplitPair : (pre ++ post).Pairwise (· < ·) := by
        simpa [hsplit] using hDpair
      exact (List.pairwise_append.mp hsplitPair).1
    have hpost'Pair : post'.Pairwise (· < ·) :=
      List.Pairwise.sublist (List.eraseIdx_sublist post k) hpostPair
    have hpost'Sub : post'.Sublist post := List.eraseIdx_sublist post k
    have hEpair : E.Pairwise (· < ·) := by
      apply List.pairwise_append.mpr
      refine ⟨hprePair, ?_, ?_⟩
      · rw [List.pairwise_cons]
        refine ⟨?_, hpost'Pair⟩
        intro p hp
        exact hpost p (hpost'Sub.mem hp)
      · intro p hp q hq
        simp only [List.mem_cons] at hq
        rcases hq with hqa | hq
        · simpa [hqa] using hpre p hp
        · exact (hpre p hp).trans (hpost q (hpost'Sub.mem hq))
    have hreplace :
        cs.simple (word a) * cs.wordProd (post'.map word) =
          cs.wordProd (post.map word) := by
      have hmapErase :
          (post.map word).eraseIdx k = post'.map word := by
        simpa [post'] using List.eraseIdx_map word post k
      rw [← hmapErase, ← hexchange]
      simp only [← mul_assoc, cs.simple_mul_simple_self, one_mul]
    have hEprod : cs.wordProd (E.map word) = w := by
      calc
        cs.wordProd (E.map word) =
            cs.wordProd (pre.map word) *
              (cs.simple (word a) * cs.wordProd (post'.map word)) := by
          simp [E, cs.wordProd_append, cs.wordProd_cons]
        _ = cs.wordProd (pre.map word) *
              cs.wordProd (post.map word) := by rw [hreplace]
        _ = cs.wordProd (D.map word) := by
          simp [hsplit, cs.wordProd_append]
        _ = w := hDprod
    have hElen : E.length = D.length := by
      have herase := List.length_eraseIdx_add_one hkPost
      simp only [E, post', List.length_append, List.length_cons,
        ]
      simp only [hsplit, List.length_append]
      omega
    have hEred : cs.IsReduced (E.map word) := by
      unfold CoxeterSystem.IsReduced
      rw [hEprod, ← hDprod, hDred.eq]
      simpa using hElen.symm
    have hlex : List.Lex (· < ·) E D := by
      rw [hsplit]
      apply List.Lex.append_left
      cases post with
      | nil => simp at hkPost
      | cons b post =>
          apply List.Lex.rel
          exact hpost b (by simp)
    exact hleftmost.2 E ⟨hEpair, hEred, hEprod⟩ hlex

/-- The converse recognition implication is purely length-theoretic: if all
local `D[a]` words are reduced, then a strictly increasing selected index
list is lexicographically first for its product. -/
theorem leftmost_of_allLocal
    {n : ℕ} (word : Fin n → B) (D : List (Fin n))
    (hDpair : D.Pairwise (· < ·))
    (hall : AreAllLocalIndexSubwordsReduced cs word D) :
    IsLeftmostReducedIndexListFor cs word
      (cs.wordProd (D.map word)) D := by
  have hDred : cs.IsReduced (D.map word) := by
    cases D with
    | nil => simp [CoxeterSystem.IsReduced]
    | cons d D =>
        have hpair := List.pairwise_cons.mp hDpair
        have hfilter :
            (d :: D).filter (fun x ↦ d < x) = D := by
          have htail : D.filter (fun x ↦ d < x) = D := by
            rw [List.filter_eq_self]
            intro x hx
            simp [hpair.1 x hx]
          simp [htail]
        simpa [hfilter] using hall d
  refine ⟨⟨hDpair, hDred, rfl⟩, ?_⟩
  intro E hE hlex
  rcases hE with ⟨hEpair, hEred, hEprod⟩
  have hlen : E.length = D.length := by
    calc
      E.length = cs.length (cs.wordProd (E.map word)) := by
        simpa using hEred.eq.symm
      _ = cs.length (cs.wordProd (D.map word)) := congrArg cs.length hEprod
      _ = D.length := by simpa using hDred.eq
  obtain ⟨P, a, E', d, D', hEsplit, hDsplit, had⟩ :=
    exists_first_difference_of_lex_of_length_eq hlex hlen
  have hEpairSplit : (P ++ a :: E').Pairwise (· < ·) := by
    simpa [hEsplit] using hEpair
  have hDpairSplit : (P ++ d :: D').Pairwise (· < ·) := by
    simpa [hDsplit] using hDpair
  have hfilter :
      D.filter (fun x ↦ a < x) = d :: D' := by
    rw [hDsplit]
    exact filter_gt_eq_suffix_at_first_difference
      hEpairSplit hDpairSplit had
  have hlocal : cs.IsReduced (word a :: (d :: D').map word) := by
    simpa [hfilter] using hall a
  have hE'tailRed : cs.IsReduced (E'.map word) := by
    let pref : List B := P.map word ++ [word a]
    have hmap : E.map word = pref ++ E'.map word := by
      simp [pref, hEsplit]
    have hdrop := hEred.drop pref.length
    rw [hmap, List.drop_append_of_le_length (le_refl pref.length),
      List.drop_length, List.nil_append] at hdrop
    exact hdrop
  have htailProd :
      cs.simple (word a) * cs.wordProd (E'.map word) =
        cs.wordProd ((d :: D').map word) := by
    apply mul_left_cancel (a := cs.wordProd (P.map word))
    simpa [hEsplit, hDsplit, cs.wordProd_append,
      cs.wordProd_cons, mul_assoc] using hEprod
  have hlocalProd :
      cs.wordProd (word a :: (d :: D').map word) =
        cs.wordProd (E'.map word) := by
    rw [cs.wordProd_cons, ← htailProd]
    simp only [← mul_assoc, cs.simple_mul_simple_self, one_mul]
  have hlength := hlocal.eq
  rw [hlocalProd, hE'tailRed.eq] at hlength
  simp [hEsplit, hDsplit] at hlen hlength
  omega

/-- Armstrong's local recognition criterion in a self-contained index-list
form.  Simple left exchange is used only in the forward implication. -/
theorem leftmost_iff_allLocal_of_simpleLeftExchange
    {n : ℕ} (word : Fin n → B) (D : List (Fin n))
    (hDpair : D.Pairwise (· < ·))
    (hExchange : HasSimpleLeftExchange cs) :
    IsLeftmostReducedIndexListFor cs word
        (cs.wordProd (D.map word)) D ↔
      AreAllLocalIndexSubwordsReduced cs word D := by
  constructor
  · exact allLocal_of_leftmost_of_simpleLeftExchange cs word
      (cs.wordProd (D.map word)) D hExchange
  · exact leftmost_of_allLocal cs word D hDpair

/-- The row-dependent position set `D[a]` from the manuscript. -/
abbrev localPositions {n : ℕ}
    (D : Finset (Fin n)) (a : Fin n) : Finset (Fin n) :=
  rowRestrictedOmissions D a

/-- Fixed-word local reducedness: every `D[a]`-subword is reduced. -/
def AreAllLocalSubwordsReduced
    (ambient : List B) (D : Finset (Fin ambient.length)) : Prop :=
  ∀ a : Fin ambient.length,
    cs.IsReduced (subwordAt ambient (localPositions D a))

/-- Filtering a finite set and then sorting agrees with filtering its sorted
list. -/
theorem filter_sort_eq_sort_filter
    {n : ℕ} (D : Finset (Fin n)) (a : Fin n) :
    (D.sort (· ≤ ·)).filter (fun d ↦ a < d) =
      (D.filter fun d ↦ a < d).sort (· ≤ ·) := by
  apply (D.sortedLT_sort.pairwise.filter _).sortedLT.eq_of_mem_iff
    (D.filter fun d ↦ a < d).sortedLT_sort
  intro x
  simp

/-- The sorted local position set starts at `a` and continues with the
selected positions strictly after `a`. -/
theorem sort_localPositions
    {n : ℕ} (D : Finset (Fin n)) (a : Fin n) :
    (localPositions D a).sort (· ≤ ·) =
      a :: (D.filter fun d ↦ a < d).sort (· ≤ ·) := by
  unfold localPositions rowRestrictedOmissions
  apply Finset.sort_insert
  · intro b hb
    exact (Finset.mem_filter.mp hb).2.le
  · simp

/-- Literal list form of a local `D[a]` subword. -/
theorem subwordAt_localPositions
    (ambient : List B) (D : Finset (Fin ambient.length))
    (a : Fin ambient.length) :
    subwordAt ambient (localPositions D a) =
      ambient.get a ::
        ((D.sort (· ≤ ·)).filter fun d ↦ a < d).map ambient.get := by
  rw [subwordAt, sort_localPositions,
    filter_sort_eq_sort_filter]
  rfl

/-- Finset local reducedness is exactly the index-list local criterion for
the sorted position list. -/
theorem allLocalSubwordsReduced_iff_indexList
    (ambient : List B) (D : Finset (Fin ambient.length)) :
    AreAllLocalSubwordsReduced cs ambient D ↔
      AreAllLocalIndexSubwordsReduced cs ambient.get
        (D.sort (· ≤ ·)) := by
  constructor <;> intro h a
  · simpa [AreAllLocalSubwordsReduced,
      AreAllLocalIndexSubwordsReduced,
      subwordAt_localPositions] using h a
  · simpa [AreAllLocalSubwordsReduced,
      AreAllLocalIndexSubwordsReduced,
      subwordAt_localPositions] using h a

/-- A finite-set reduced-subword witness is the same witness carried by its
strictly increasing sorted index list. -/
theorem reducedSubwordFor_iff_reducedIndexList_sort
    (ambient : List B) (w : W)
    (D : Finset (Fin ambient.length)) :
    IsReducedSubwordFor cs ambient w D ↔
      IsReducedIndexListFor cs ambient.get w (D.sort (· ≤ ·)) := by
  constructor
  · rintro ⟨hred, hprod⟩
    exact ⟨D.sortedLT_sort.pairwise, hred, hprod⟩
  · rintro ⟨_, hred, hprod⟩
    exact ⟨hred, hprod⟩

/-- Existing finite-set leftmost witnesses and leftmost strictly increasing
index-list witnesses coincide. -/
theorem leftmostReducedSubwordFor_iff_leftmostIndexList_sort
    (ambient : List B) (w : W)
    (D : Finset (Fin ambient.length)) :
    IsLeftmostReducedSubwordFor cs ambient w D ↔
      IsLeftmostReducedIndexListFor cs ambient.get w
        (D.sort (· ≤ ·)) := by
  constructor
  · rintro ⟨hD, hminimal⟩
    refine ⟨(reducedSubwordFor_iff_reducedIndexList_sort
      cs ambient w D).mp hD, ?_⟩
    intro E hE hlex
    have hEnodup : E.Nodup := hE.1.nodup
    have hEsort : E.toFinset.sort (· ≤ ·) = E :=
      (List.toFinset_sort (· ≤ ·) hEnodup).2
        (hE.1.imp fun h ↦ le_of_lt h)
    have hEfin :
        IsReducedSubwordFor cs ambient w E.toFinset := by
      apply (reducedSubwordFor_iff_reducedIndexList_sort
        cs ambient w E.toFinset).mpr
      simpa [hEsort] using hE
    exact hminimal E.toFinset hEfin (by simpa [hEsort] using hlex)
  · rintro ⟨hD, hminimal⟩
    refine ⟨(reducedSubwordFor_iff_reducedIndexList_sort
      cs ambient w D).mpr hD, ?_⟩
    intro E hE hlex
    exact hminimal (E.sort (· ≤ ·))
      ((reducedSubwordFor_iff_reducedIndexList_sort
        cs ambient w E).mp hE) hlex

/-- Armstrong's fixed-word recognition criterion in the repository's
finite-set interface, conditional only on simple left exchange. -/
theorem leftmostReducedSubwordFor_iff_allLocal_of_simpleLeftExchange
    (ambient : List B) (D : Finset (Fin ambient.length))
    (hExchange : HasSimpleLeftExchange cs) :
    IsLeftmostReducedSubwordFor cs ambient
        (cs.wordProd (subwordAt ambient D)) D ↔
      AreAllLocalSubwordsReduced cs ambient D := by
  rw [leftmostReducedSubwordFor_iff_leftmostIndexList_sort,
    allLocalSubwordsReduced_iff_indexList]
  exact leftmost_iff_allLocal_of_simpleLeftExchange cs ambient.get
    (D.sort (· ≤ ·)) D.sortedLT_sort.pairwise hExchange

/-- Arbitrary-element form: `D` is the leftmost reduced position set for
`w` exactly when it represents `w` and satisfies every local criterion. -/
theorem leftmostReducedSubwordFor_iff_product_eq_and_allLocal_of_simpleLeftExchange
    (ambient : List B) (w : W)
    (D : Finset (Fin ambient.length))
    (hExchange : HasSimpleLeftExchange cs) :
    IsLeftmostReducedSubwordFor cs ambient w D ↔
      cs.wordProd (subwordAt ambient D) = w ∧
        AreAllLocalSubwordsReduced cs ambient D := by
  constructor
  · intro hleft
    have hprod := hleft.1.2
    refine ⟨hprod, ?_⟩
    apply (leftmostReducedSubwordFor_iff_allLocal_of_simpleLeftExchange
      cs ambient D hExchange).mp
    simpa [hprod] using hleft
  · rintro ⟨hprod, hlocal⟩
    have hpinned :=
      (leftmostReducedSubwordFor_iff_allLocal_of_simpleLeftExchange
        cs ambient D hExchange).mpr hlocal
    simpa [hprod] using hpinned

section SimpleGraph

open SimpleGraphCoxeter WordRootProcess RootSignStrategy

universe uL

variable {L : Type uL} [Fintype L]

/-- The compiled Tits theorem reduces simple right exchange to the remaining
reflection-transport identity for the geometric representation. -/
theorem hasSimpleRightExchange_of_rootTransport
    (G : SimpleGraph L)
    (htransport : RootTransportDeterminesReflection G) :
    HasSimpleRightExchange (system G) := by
  intro Q i hQ hright
  have hnegative :
      IsNegative
        (geometricRepresentation G (wordProd G Q) (simpleRoot i)) :=
    rightDescentImpliesNegativeRoot_of_reducedWordsPositive G
      (reducedWordsHavePositiveInversionRoots G)
      (wordProd G Q) i hright
  obtain ⟨k, hk, hdelete⟩ :=
    exists_eraseIdx_of_wordRoot_negative G
      (realRootSignDichotomy G) htransport Q i hnegative
  refine ⟨Q.take k, Q[k], Q.drop (k + 1), ?_, ?_⟩
  · calc
      Q = Q.take (k + 1) ++ Q.drop (k + 1) :=
        (List.take_append_drop (k + 1) Q).symm
      _ = (Q.take k ++ [Q[k]]) ++ Q.drop (k + 1) := by
        rw [List.take_concat_get' Q k hk]
      _ = Q.take k ++ Q[k] :: Q.drop (k + 1) := by simp
  · calc
      (system G).wordProd Q * (system G).simple i =
          wordProd G (Q.concat i) := by
        exact ((system G).wordProd_concat i Q).symm
      _ = wordProd G (Q.eraseIdx k) := hdelete
      _ = (system G).wordProd (Q.take k ++ Q.drop (k + 1)) := by
        rw [List.eraseIdx_eq_take_drop_succ]
        rfl

/-- Thus the same single geometric reflection-transport identity also
supplies the left exchange statement used by sorting. -/
theorem hasSimpleLeftExchange_of_rootTransport
    (G : SimpleGraph L)
    (htransport : RootTransportDeterminesReflection G) :
    HasSimpleLeftExchange (system G) :=
  hasSimpleLeftExchange_of_hasSimpleRightExchange (system G)
    (hasSimpleRightExchange_of_rootTransport G htransport)

/-- Simple right exchange for every finite simple graph, unconditionally. -/
theorem hasSimpleRightExchange_simpleGraph
    (G : SimpleGraph L) :
    HasSimpleRightExchange (system G) :=
  hasSimpleRightExchange_of_rootTransport G
    (rootTransportDeterminesReflection G)

/-- Simple left exchange for every finite simple graph, unconditionally. -/
theorem hasSimpleLeftExchange_simpleGraph
    (G : SimpleGraph L) :
    HasSimpleLeftExchange (system G) :=
  hasSimpleLeftExchange_of_rootTransport G
    (rootTransportDeterminesReflection G)

/-- Unconditional indexed simple left exchange for the Coxeter system of a
finite simple graph. -/
theorem exists_eraseIdx_of_simpleLeftExchange_simpleGraph
    (G : SimpleGraph L) (Q : List L) (i : L)
    (hQ : IsReduced G Q)
    (hdescent : (system G).IsLeftDescent (wordProd G Q) i) :
    ∃ k, k < Q.length ∧
      (system G).simple i * wordProd G Q =
        wordProd G (Q.eraseIdx k) := by
  exact exists_eraseIdx_of_simpleLeftExchange (system G)
    (hasSimpleLeftExchange_simpleGraph G) Q i hQ hdescent

/-- Unconditional fixed-word local recognition for every finite simple
graph; the ambient word itself need not be reduced. -/
theorem leftmostReducedSubwordFor_iff_allLocal_simpleGraph
    (G : SimpleGraph L) (ambient : List L)
    (D : Finset (Fin ambient.length)) :
    IsLeftmostReducedSubwordFor (system G) ambient
        ((system G).wordProd (subwordAt ambient D)) D ↔
      AreAllLocalSubwordsReduced (system G) ambient D :=
  leftmostReducedSubwordFor_iff_allLocal_of_simpleLeftExchange
    (system G) ambient D (hasSimpleLeftExchange_simpleGraph G)

/-- Arbitrary represented-element form of the unconditional graph
recognition theorem. -/
theorem leftmostReducedSubwordFor_iff_product_eq_and_allLocal_simpleGraph
    (G : SimpleGraph L) (ambient : List L) (w : Group G)
    (D : Finset (Fin ambient.length)) :
    IsLeftmostReducedSubwordFor (system G) ambient w D ↔
      (system G).wordProd (subwordAt ambient D) = w ∧
        AreAllLocalSubwordsReduced (system G) ambient D :=
  leftmostReducedSubwordFor_iff_product_eq_and_allLocal_of_simpleLeftExchange
    (system G) ambient w D (hasSimpleLeftExchange_simpleGraph G)

end SimpleGraph


end QuotientSubmoduleEquidistribution.RepresentationDirected.SortingExchange
