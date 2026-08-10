import OpConjecture.RepresentationDirected.SimpleGraphBruhat

set_option autoImplicit false

noncomputable section

namespace OpConjecture.RepresentationDirected.OppositeSubmodule

open OpConjecture.RepresentationDirected.FixedWord
open FixedWordSubwords
open FixedWordProfile
open SimpleGraphBruhat
open SimpleGraphCoxeter

universe uL

variable {L : Type uL} [Fintype L]

omit [Fintype L] in
/-- Reversal preserves reducedness of a Coxeter word. -/
theorem isReduced_reverse_iff (G : SimpleGraph L) (Q : List L) :
    IsReduced G Q.reverse ↔ IsReduced G Q := by
  change (system G).IsReduced Q.reverse ↔ (system G).IsReduced Q
  simp

/-- A reduced subword witness reverses to a witness for the inverse in the
reversed ambient word. -/
theorem bruhatLE_inv_reverse
    (G : SimpleGraph L) (Q : List L) (hQ : IsReduced G Q)
    (u : Group G) (hu : BruhatLE G u (wordProd G Q)) :
    BruhatLE G u⁻¹ (wordProd G Q.reverse) := by
  let hQr : IsReduced G Q.reverse :=
    (isReduced_reverse_iff G Q).2 hQ
  obtain ⟨D, hD⟩ :=
    (bruhatLE_iff_exists_reducedSubwordFor G Q hQ u).mp hu
  apply (bruhatLE_iff_exists_reducedSubwordFor
    G Q.reverse hQr u⁻¹).2
  exact ⟨reversePositionsIn Q D,
    (isReducedSubwordFor_reverse_iff
      (system G) Q u D).2 hD⟩

/-- In a reduced ambient word, taking inverses identifies the principal
Bruhat interval with the interval for the reversed word. -/
theorem bruhatLE_inv_reverse_iff
    (G : SimpleGraph L) (Q : List L) (hQ : IsReduced G Q)
    (u : Group G) :
    BruhatLE G u⁻¹ (wordProd G Q.reverse) ↔
      BruhatLE G u (wordProd G Q) := by
  constructor
  · intro hu
    have hQr : IsReduced G Q.reverse :=
      (isReduced_reverse_iff G Q).2 hQ
    simpa using bruhatLE_inv_reverse G Q.reverse hQr u⁻¹ hu
  · exact bruhatLE_inv_reverse G Q hQ u

/-- The inversion equivalence between a principal Bruhat interval and the
principal interval of the reversed reduced word. -/
def bruhatLowerIntervalReverseEquiv
    (G : SimpleGraph L) (Q : List L) (hQ : IsReduced G Q) :
    BruhatLowerInterval G Q ≃ BruhatLowerInterval G Q.reverse where
  toFun u := ⟨u.1⁻¹,
    (bruhatLE_inv_reverse_iff G Q hQ u.1).2 u.2⟩
  invFun v := ⟨v.1⁻¹, by
    have hQr : IsReduced G Q.reverse :=
      (isReduced_reverse_iff G Q).2 hQ
    simpa using bruhatLE_inv_reverse G Q.reverse hQr v.1 v.2⟩
  left_inv u := by
    apply Subtype.ext
    simp
  right_inv v := by
    apply Subtype.ext
    simp

/-! ## Position reversal back to the original word -/

/-- Pull a position set in `Q.reverse` back to the corresponding positions
of `Q`. -/
def unreversePositionsIn
    {B : Type*} (Q : List B)
    (positions : Finset (Fin Q.reverse.length)) :
    Finset (Fin Q.length) :=
  positions.map (reverseIndexEquiv Q).symm.toEmbedding

@[simp]
theorem card_unreversePositionsIn
    {B : Type*} (Q : List B)
    (positions : Finset (Fin Q.reverse.length)) :
    (unreversePositionsIn Q positions).card = positions.card := by
  simp [unreversePositionsIn]

@[simp]
theorem reversePositionsIn_unreversePositionsIn
    {B : Type*} (Q : List B)
    (positions : Finset (Fin Q.reverse.length)) :
    reversePositionsIn Q (unreversePositionsIn Q positions) = positions := by
  ext i
  simp [unreversePositionsIn, reversePositionsIn]

@[simp]
theorem unreversePositionsIn_reversePositionsIn
    {B : Type*} (Q : List B)
    (positions : Finset (Fin Q.length)) :
    unreversePositionsIn Q (reversePositionsIn Q positions) = positions := by
  ext i
  simp [unreversePositionsIn, reversePositionsIn]

/-- Selecting pulled-back positions from `Q` reverses the selected subword
inside `Q.reverse`. -/
theorem subwordAt_unreversePositionsIn
    {B : Type*} (Q : List B)
    (positions : Finset (Fin Q.reverse.length)) :
    subwordAt Q (unreversePositionsIn Q positions) =
      (subwordAt Q.reverse positions).reverse := by
  have h := subwordAt_reverse Q (unreversePositionsIn Q positions)
  simpa using (congrArg List.reverse h).symm

/-- A reduced witness in the reversed word pulls back to a reduced witness
for the inverse in the original word. -/
theorem isReducedSubwordFor_unreverse_iff
    {B W : Type*} [Group W] {M : CoxeterMatrix B}
    (cs : CoxeterSystem M W) (Q : List B) (w : W)
    (positions : Finset (Fin Q.reverse.length)) :
    IsReducedSubwordFor cs Q w⁻¹
        (unreversePositionsIn Q positions) ↔
      IsReducedSubwordFor cs Q.reverse w positions := by
  constructor
  · intro h
    have hr :=
      (isReducedSubwordFor_reverse_iff cs Q w⁻¹
        (unreversePositionsIn Q positions)).2 h
    simpa using hr
  · intro h
    have hr :=
      (isReducedSubwordFor_reverse_iff cs Q w⁻¹
        (unreversePositionsIn Q positions)).1
    apply hr
    simpa using h

/-! ## The colex-last position set obtained from the reversed word -/

/-- The chosen Bruhat positions satisfy the advertised lex-first property. -/
theorem bruhatLexFirstPositions_spec
    (G : SimpleGraph L) (Q : List L) (hQ : IsReduced G Q)
    (u : BruhatLowerInterval G Q) :
    IsLeftmostReducedSubwordFor (system G) Q u.1
      (bruhatLexFirstPositions G Q hQ u) := by
  let v : FixedWordElement (system G) Q :=
    (fixedWordElementEquivBruhatLowerInterval G Q hQ).symm u
  change IsLeftmostReducedSubwordFor (system G) Q v.1
    (lexFirstPositions (system G) Q v)
  exact lexFirstPositions_spec (system G) Q v

/-- The manuscript's colex-last candidate: invert the Bruhat element, take
the lex-first reduced positions in `Q.reverse`, and reverse those positions
back into `Q`. -/
def bruhatColexLastPositions
    (G : SimpleGraph L) (Q : List L) (hQ : IsReduced G Q)
    (u : BruhatLowerInterval G Q) : Finset (Fin Q.length) :=
  let hQr : IsReduced G Q.reverse :=
    (isReduced_reverse_iff G Q).2 hQ
  unreversePositionsIn Q
    (bruhatLexFirstPositions G Q.reverse hQr
      (bruhatLowerIntervalReverseEquiv G Q hQ u))

/-- The colex-last candidate is a reduced subword for the original Bruhat
element. -/
theorem bruhatColexLastPositions_reduced
    (G : SimpleGraph L) (Q : List L) (hQ : IsReduced G Q)
    (u : BruhatLowerInterval G Q) :
    IsReducedSubwordFor (system G) Q u.1
      (bruhatColexLastPositions G Q hQ u) := by
  let hQr : IsReduced G Q.reverse :=
    (isReduced_reverse_iff G Q).2 hQ
  let uR : BruhatLowerInterval G Q.reverse :=
    bruhatLowerIntervalReverseEquiv G Q hQ u
  have hlex := (bruhatLexFirstPositions_spec G Q.reverse hQr uR).1
  have hpull :=
    (isReducedSubwordFor_unreverse_iff
      (system G) Q uR.1
      (bruhatLexFirstPositions G Q.reverse hQr uR)).2 hlex
  simpa [bruhatColexLastPositions, hQr, uR,
    bruhatLowerIntervalReverseEquiv] using hpull

/-- Both canonical position sets omit exactly the Coxeter length. -/
theorem card_bruhatColexLastPositions
    (G : SimpleGraph L) (Q : List L) (hQ : IsReduced G Q)
    (u : BruhatLowerInterval G Q) :
    (bruhatColexLastPositions G Q hQ u).card =
      (system G).length u.1 := by
  let hQr : IsReduced G Q.reverse :=
    (isReduced_reverse_iff G Q).2 hQ
  rw [bruhatColexLastPositions, card_unreversePositionsIn,
    card_bruhatLexFirstPositions]
  exact (system G).length_inv u.1

/-! ## Exact reverse-lexicographic extremality -/

/-- Reverse lexicographic comparison of increasing position tuples: inspect
the tuples from their largest entries toward their smallest entries. -/
def ReverseLexLT {n : ℕ}
    (D E : Finset (Fin n)) : Prop :=
  List.Lex (· < ·)
    (D.sort (· ≤ ·)).reverse
    (E.sort (· ≤ ·)).reverse

/-- Mapping a lex comparison along a relation-preserving function preserves
the lex comparison. -/
theorem listLex_map_of_imp
    {A B : Type*} {r : A → A → Prop} {s : B → B → Prop}
    (f : A → B) (hf : ∀ {a b}, r a b → s (f a) (f b))
    {l m : List A} (h : List.Lex r l m) :
    List.Lex s (l.map f) (m.map f) := by
  induction h with
  | nil => exact .nil
  | rel hab => exact .rel (hf hab)
  | cons _ ih => exact .cons ih

/-- On equal-length lists, a lex comparison for the reversed relation is the
opposite lex comparison. -/
theorem listLex_swap_of_length_eq
    {A : Type*} {r : A → A → Prop}
    {l m : List A}
    (h : List.Lex (fun a b ↦ r b a) l m)
    (hlen : l.length = m.length) :
    List.Lex r m l := by
  induction h with
  | nil => simp at hlen
  | rel hab => exact .rel hab
  | cons h ih =>
      exact .cons (ih (Nat.succ.inj hlen))

/-- A strict antitone map reverses lex order on equal-length lists. -/
theorem listLex_map_strictAnti
    {A B : Type*} [LinearOrder A] [LinearOrder B]
    {f : A → B} (hf : StrictAnti f)
    {l m : List A} (hlen : l.length = m.length)
    (h : List.Lex (· < ·) l m) :
    List.Lex (· < ·) (m.map f) (l.map f) := by
  have hmapped :
      List.Lex (fun x y : B ↦ y < x) (l.map f) (m.map f) :=
    listLex_map_of_imp
      (r := fun x y : A ↦ x < y)
      (s := fun x y : B ↦ y < x)
      f (fun hab ↦ hf hab) h
  apply listLex_swap_of_length_eq (r := fun x y : B ↦ x < y) hmapped
  simp [hlen]

/-- The inverse of the position-reversal equivalence is again strictly
antitone. -/
theorem reverseIndexEquiv_symm_strictAnti
    {B : Type*} (Q : List B) :
    StrictAnti (reverseIndexEquiv Q).symm := by
  let hf := reverseIndexEquiv_strictAnti Q
  intro i j hij
  apply (hf.lt_iff_gt).mp
  simpa using hij

/-- Sorting a pulled-back reversed position set is the reverse of mapping
the sorted reversed positions back to the original word. -/
theorem sort_unreversePositionsIn
    {B : Type*} (Q : List B)
    (positions : Finset (Fin Q.reverse.length)) :
    (unreversePositionsIn Q positions).sort (· ≤ ·) =
      ((positions.sort (· ≤ ·)).map
        (reverseIndexEquiv Q).symm).reverse := by
  let e := (reverseIndexEquiv Q).symm
  have hdescending :
      ((positions.sort (· ≤ ·)).map e).SortedGT := by
    rw [List.sortedGT_iff_pairwise, List.pairwise_map]
    exact positions.sortedLT_sort.pairwise.imp
      fun hij ↦ reverseIndexEquiv_symm_strictAnti Q hij
  have hmembership :
      ∀ i : Fin Q.length,
        i ∈ (positions.sort (· ≤ ·)).map e ↔
          i ∈ (unreversePositionsIn Q positions).sort (· ≤ ·) := by
    intro i
    simp only [List.mem_map, Finset.mem_sort,
      unreversePositionsIn, Finset.mem_map, Equiv.coe_toEmbedding, e]
  have hmapped :
      (positions.sort (· ≤ ·)).map e =
        ((unreversePositionsIn Q positions).sort (· ≤ ·)).reverse :=
    hdescending.eq_reverse_of_mem_iff_of_sortedLT
      hmembership
      (unreversePositionsIn Q positions).sortedLT_sort
  simpa using congrArg List.reverse hmapped.symm

/-- Position reversal changes lex order on the reversed word into reverse
lexicographic order on the original word, for equal-cardinality sets. -/
theorem reverseLexLT_unreverse_iff
    {B : Type*} (Q : List B)
    (P E : Finset (Fin Q.reverse.length))
    (hcard : P.card = E.card) :
    ReverseLexLT (unreversePositionsIn Q P)
        (unreversePositionsIn Q E) ↔
      List.Lex (· < ·)
        (E.sort (· ≤ ·)) (P.sort (· ≤ ·)) := by
  rw [ReverseLexLT, sort_unreversePositionsIn,
    sort_unreversePositionsIn]
  simp only [List.reverse_reverse]
  constructor
  · intro h
    have hlen :
        ((P.sort (· ≤ ·)).map
          (reverseIndexEquiv Q).symm).length =
        ((E.sort (· ≤ ·)).map
          (reverseIndexEquiv Q).symm).length := by
      simp [Finset.length_sort, hcard]
    have hmapped := listLex_map_strictAnti
      (reverseIndexEquiv_strictAnti Q) hlen h
    simpa [List.map_map] using hmapped
  · intro h
    have hlen :
        (E.sort (· ≤ ·)).length =
          (P.sort (· ≤ ·)).length := by
      simp [Finset.length_sort, hcard]
    exact listLex_map_strictAnti
      (reverseIndexEquiv_symm_strictAnti Q) hlen h

/-- Every reduced position witness has cardinality equal to Coxeter length. -/
theorem card_eq_length_of_isReducedSubwordFor
    {B W : Type*} [Group W] {M : CoxeterMatrix B}
    (cs : CoxeterSystem M W) (Q : List B) (w : W)
    (D : Finset (Fin Q.length))
    (hD : IsReducedSubwordFor cs Q w D) :
    D.card = cs.length w := by
  calc
    D.card = (subwordAt Q D).length :=
      (length_subwordAt Q D).symm
    _ = cs.length (cs.wordProd (subwordAt Q D)) :=
      hD.1.eq.symm
    _ = cs.length w := by rw [hD.2]

/-- A reduced position set is colex-last when no other reduced witness is
larger in reverse lexicographic order. -/
def IsColexLastReducedSubwordFor
    {B W : Type*} [Group W] {M : CoxeterMatrix B}
    (cs : CoxeterSystem M W) (Q : List B) (w : W)
    (D : Finset (Fin Q.length)) : Prop :=
  IsReducedSubwordFor cs Q w D ∧
    ∀ E : Finset (Fin Q.length),
      IsReducedSubwordFor cs Q w E →
        ¬ ReverseLexLT D E

/-- Reversal of the lex-first witness for the inverse is exactly the
colex-last reduced witness for the original Bruhat element. -/
theorem bruhatColexLastPositions_spec
    (G : SimpleGraph L) (Q : List L) (hQ : IsReduced G Q)
    (u : BruhatLowerInterval G Q) :
    IsColexLastReducedSubwordFor (system G) Q u.1
      (bruhatColexLastPositions G Q hQ u) := by
  let hQr : IsReduced G Q.reverse :=
    (isReduced_reverse_iff G Q).2 hQ
  let uR : BruhatLowerInterval G Q.reverse :=
    bruhatLowerIntervalReverseEquiv G Q hQ u
  let P : Finset (Fin Q.reverse.length) :=
    bruhatLexFirstPositions G Q.reverse hQr uR
  have hPleft :
      IsLeftmostReducedSubwordFor (system G) Q.reverse uR.1 P :=
    bruhatLexFirstPositions_spec G Q.reverse hQr uR
  refine ⟨bruhatColexLastPositions_reduced G Q hQ u, ?_⟩
  intro E hE hCandidateE
  let ER : Finset (Fin Q.reverse.length) :=
    reversePositionsIn Q E
  have hER :
      IsReducedSubwordFor (system G) Q.reverse uR.1 ER := by
    have hrev :=
      (isReducedSubwordFor_reverse_iff
        (system G) Q u.1 E).2 hE
    simpa [ER, uR, bruhatLowerIntervalReverseEquiv] using hrev
  have hcard : P.card = ER.card := by
    rw [card_eq_length_of_isReducedSubwordFor
      (system G) Q.reverse uR.1 P hPleft.1,
      card_eq_length_of_isReducedSubwordFor
        (system G) Q.reverse uR.1 ER hER]
  have hRelation :
      ReverseLexLT (unreversePositionsIn Q P)
        (unreversePositionsIn Q ER) := by
    simpa [P, ER, bruhatColexLastPositions, hQr, uR] using
      hCandidateE
  exact hPleft.2 ER hER
    ((reverseLexLT_unreverse_iff Q P ER hcard).1 hRelation)

end OpConjecture.RepresentationDirected.OppositeSubmodule
