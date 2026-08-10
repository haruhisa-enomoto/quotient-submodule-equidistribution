import QuotientSubmoduleEquidistribution.RepresentationDirected.SimpleGraphGeometricRepresentation
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!
# Coxeter comparison and edge-deletion infrastructure

Abstract Coxeter steps used in
`lem:directed-delete-separated-edge` and
`prop:directed-segment-reduced`.  It contains no algebra or module example.
-/

noncomputable section

namespace QuotientSubmoduleEquidistribution.RepresentationDirected.SegmentReducedness

open QuotientSubmoduleEquidistribution.RepresentationDirected.SimpleGraphCoxeter

universe uS uL uA uB uW₁ uW₂

/-! ## A Coxeter graph pulled back along an arbitrary label map -/

/-- The graph on `S` in which two vertices are adjacent exactly when their
images under `pi` are adjacent in `G`.  Injectivity of `pi` is not required.
In particular, distinct vertices with the same image are nonadjacent. -/
def pullbackGraph {S : Type uS} {L : Type uL}
    (G : SimpleGraph L) (pi : S → L) : SimpleGraph S where
  Adj A B := G.Adj (pi A) (pi B)
  symm := ⟨fun A B h ↦ G.symm.symm (pi A) (pi B) h⟩
  loopless := ⟨fun A h ↦ G.loopless.irrefl (pi A) h⟩

@[simp] theorem pullbackGraph_adj {S : Type uS} {L : Type uL}
    (G : SimpleGraph L) (pi : S → L) (A B : S) :
    (pullbackGraph G pi).Adj A B ↔ G.Adj (pi A) (pi B) :=
  Iff.rfl

/-- The original simple reflections satisfy the relations of the pulled-back
graph.  This includes the case of two distinct segment vertices having the
same original label: their commuting relation maps to `s_i^2 = 1`. -/
theorem projectSimple_isLiftable
    {S : Type uS} {L : Type uL}
    (G : SimpleGraph L) (pi : S → L) :
    CoxeterMatrix.IsLiftable (matrix (pullbackGraph G pi))
      (fun A ↦ (system G).simple (pi A)) := by
  intro A B
  by_cases hAB : A = B
  · subst B
    rw [matrix_apply_self, pow_one]
    exact (system G).simple_mul_simple_self (pi A)
  · by_cases hAdj : G.Adj (pi A) (pi B)
    · rw [matrix_apply_of_adj (pullbackGraph G pi)
          (show (pullbackGraph G pi).Adj A B from hAdj)]
      have hTarget : matrix G (pi A) (pi B) = 3 :=
        matrix_apply_of_adj G hAdj
      rw [← hTarget]
      exact (system G).simple_mul_simple_pow (pi A) (pi B)
    · rw [matrix_apply_of_ne_of_not_adj (G := pullbackGraph G pi)
          hAB (show ¬(pullbackGraph G pi).Adj A B from hAdj)]
      by_cases hpi : pi A = pi B
      · change
          ((system G).simple (pi A) * (system G).simple (pi B)) ^ 2 = 1
        rw [hpi]
        rw [(system G).simple_mul_simple_self, one_pow]
      · have hTarget : matrix G (pi A) (pi B) = 2 :=
          matrix_apply_of_ne_of_not_adj G hpi hAdj
        rw [← hTarget]
        exact (system G).simple_mul_simple_pow (pi A) (pi B)

/-- The canonical homomorphism from the pulled-back Coxeter group to the
original graph Coxeter group, sending each segment reflection to the simple
reflection of its original label. -/
def projectLift {S : Type uS} {L : Type uL}
    (G : SimpleGraph L) (pi : S → L) :
    Group (pullbackGraph G pi) →* Group G :=
  (system (pullbackGraph G pi)).lift
    ⟨fun A ↦ (system G).simple (pi A), projectSimple_isLiftable G pi⟩

@[simp] theorem projectLift_simple {S : Type uS} {L : Type uL}
    (G : SimpleGraph L) (pi : S → L) (A : S) :
    projectLift G pi ((system (pullbackGraph G pi)).simple A) =
      (system G).simple (pi A) := by
  exact (system (pullbackGraph G pi)).lift_apply_simple
    (projectSimple_isLiftable G pi) A

/-- A homomorphism which maps simple generators according to a label map
maps every word product to the relabelled word product. -/
theorem map_wordProd
    {A : Type uA} {B : Type uB}
    {W₁ : Type uW₁} {W₂ : Type uW₂}
    [Group W₁] [Group W₂]
    {M₁ : CoxeterMatrix A} {M₂ : CoxeterMatrix B}
    (cs₁ : CoxeterSystem M₁ W₁) (cs₂ : CoxeterSystem M₂ W₂)
    (f : A → B) (phi : W₁ →* W₂)
    (hphi : ∀ i, phi (cs₁.simple i) = cs₂.simple (f i))
    (Q : List A) :
    phi (cs₁.wordProd Q) = cs₂.wordProd (Q.map f) := by
  induction Q with
  | nil => simp
  | cons i Q ih =>
      rw [cs₁.wordProd_cons, map_mul, hphi, ih, List.map_cons,
        cs₂.wordProd_cons]

/-- Mapping every simple generator to a simple generator cannot increase
Coxeter length. -/
theorem length_map_le
    {A : Type uA} {B : Type uB}
    {W₁ : Type uW₁} {W₂ : Type uW₂}
    [Group W₁] [Group W₂]
    {M₁ : CoxeterMatrix A} {M₂ : CoxeterMatrix B}
    (cs₁ : CoxeterSystem M₁ W₁) (cs₂ : CoxeterSystem M₂ W₂)
    (f : A → B) (phi : W₁ →* W₂)
    (hphi : ∀ i, phi (cs₁.simple i) = cs₂.simple (f i))
    (w : W₁) :
    cs₂.length (phi w) ≤ cs₁.length w := by
  obtain ⟨Q, hReduced, rfl⟩ := cs₁.exists_isReduced w
  rw [map_wordProd cs₁ cs₂ f phi hphi]
  calc
    cs₂.length (cs₂.wordProd (Q.map f)) ≤ (Q.map f).length :=
      cs₂.length_wordProd_le _
    _ = Q.length := by simp
    _ = cs₁.length (cs₁.wordProd Q) := hReduced.symm

/-- If the relabelled word is reduced in the original graph, then the word
is reduced in the pulled-back graph.  This is the complete first paragraph
of `prop:directed-segment-reduced`. -/
theorem isReduced_pullback_of_map_isReduced
    {S : Type uS} {L : Type uL}
    (G : SimpleGraph L) (pi : S → L) (Q : List S)
    (hReduced : IsReduced G (Q.map pi)) :
    IsReduced (pullbackGraph G pi) Q := by
  let csS := system (pullbackGraph G pi)
  let csL := system G
  let phi := projectLift G pi
  have hMap : phi (csS.wordProd Q) = csL.wordProd (Q.map pi) :=
    map_wordProd csS csL pi phi (projectLift_simple G pi) Q
  have hLower : Q.length ≤ csS.length (csS.wordProd Q) := by
    calc
      Q.length = (Q.map pi).length := by simp
      _ = csL.length (csL.wordProd (Q.map pi)) := hReduced.symm
      _ = csL.length (phi (csS.wordProd Q)) := by rw [hMap]
      _ ≤ csS.length (csS.wordProd Q) :=
        length_map_le csS csL pi phi (projectLift_simple G pi) _
  exact Nat.le_antisymm (csS.length_wordProd_le Q) hLower

/-! ## Word-action orientation and one-edge coordinate comparison -/

/-- Apply a graph-label word through the integral geometric representation.
With the repository's left action, `actWord G (u ++ v) z` applies `v` first
and then `u`. -/
def actWord {L : Type uL} [Fintype L]
    (G : SimpleGraph L) (Q : List L) (z : RootLattice L) :
    RootLattice L :=
  geometricRepresentation G ((system G).wordProd Q) z

@[simp] theorem actWord_nil {L : Type uL} [Fintype L]
    (G : SimpleGraph L) (z : RootLattice L) :
    actWord G [] z = z := by
  simp [actWord]

theorem actWord_cons {L : Type uL} [Fintype L]
    (G : SimpleGraph L) (i : L) (Q : List L) (z : RootLattice L) :
    actWord G (i :: Q) z = simpleReflection G i (actWord G Q z) := by
  simp only [actWord, (system G).wordProd_cons, map_mul,
    LinearEquiv.mul_apply, geometricRepresentation_simple,
    simpleReflectionEquiv_apply]

theorem actWord_append {L : Type uL} [Fintype L]
    (G : SimpleGraph L) (u v : List L) (z : RootLattice L) :
    actWord G (u ++ v) z = actWord G u (actWord G v z) := by
  simp only [actWord, (system G).wordProd_append, map_mul,
    LinearEquiv.mul_apply]

/-- A word with no occurrence of `b` fixes the `b`-coordinate. -/
theorem actWord_apply_of_not_mem {L : Type uL} [Fintype L]
    (G : SimpleGraph L) {b : L} (Q : List L) (z : RootLattice L)
    (hb : b ∉ Q) :
    actWord G Q z b = z b := by
  induction Q with
  | nil => simp
  | cons i Q ih =>
      have hbi : b ≠ i := by
        intro h
        apply hb
        simp [h]
      have hbQ : b ∉ Q := by
        intro h
        exact hb (List.mem_cons_of_mem i h)
      rw [actWord_cons, simpleReflection_apply_of_ne G hbi, ih hbQ]

/-- Delete the single unoriented edge `a-b`. -/
def deleteEdge {L : Type uL} (G : SimpleGraph L) (a b : L) :
    SimpleGraph L :=
  G.deleteEdges {s(a, b)}

@[simp] theorem deleteEdge_adj {L : Type uL}
    (G : SimpleGraph L) (a b i j : L) :
    (deleteEdge G a b).Adj i j ↔
      G.Adj i j ∧ s(i, j) ≠ s(a, b) := by
  simp [deleteEdge]

/-- Away from reflections at `b`, deleting `a-b` does not change a neighbor
sum on a vector whose `b`-coordinate is zero. -/
theorem neighborSum_deleteEdge_eq_of_ne_of_coord_eq_zero
    {L : Type uL} [Fintype L]
    (G : SimpleGraph L) (a b i : L) (z : RootLattice L)
    (hib : i ≠ b) (hzb : z b = 0) :
    neighborSum (deleteEdge G a b) i z = neighborSum G i z := by
  classical
  unfold neighborSum
  apply Finset.sum_subset
  · intro h hh
    rw [(deleteEdge G a b).mem_neighborFinset] at hh
    rw [G.mem_neighborFinset]
    exact (deleteEdge_adj G a b i h).1 hh |>.1
  · intro h hhG hhDelete
    rw [G.mem_neighborFinset] at hhG
    have hEdge : s(i, h) = s(a, b) := by
      by_contra hne
      apply hhDelete
      rw [(deleteEdge G a b).mem_neighborFinset]
      exact (deleteEdge_adj G a b i h).2 ⟨hhG, hne⟩
    rcases (Sym2.eq_iff.mp hEdge) with hia | hib'
    · rw [hia.2, hzb]
    · exact False.elim (hib hib'.1)

/-- Away from a reflection at `b`, the deleted-edge reflection agrees with
the original reflection whenever the input has zero `b`-coordinate. -/
theorem simpleReflection_deleteEdge_eq_of_ne_of_coord_eq_zero
    {L : Type uL} [Fintype L]
    (G : SimpleGraph L) (a b i : L) (z : RootLattice L)
    (hib : i ≠ b) (hzb : z b = 0) :
    simpleReflection (deleteEdge G a b) i z = simpleReflection G i z := by
  funext j
  by_cases hji : j = i
  · subst j
    rw [simpleReflection_apply_self, simpleReflection_apply_self,
      neighborSum_deleteEdge_eq_of_ne_of_coord_eq_zero G a b i z hib hzb]
  · rw [simpleReflection_apply_of_ne _ hji,
      simpleReflection_apply_of_ne _ hji]

/-- If `u` contains no `b`, then deleting `a-b` does not change the action
of `u` on a vector with zero `b`-coordinate. -/
theorem actWord_deleteEdge_eq_of_not_mem_of_coord_eq_zero
    {L : Type uL} [Fintype L]
    (G : SimpleGraph L) (a b : L) (u : List L) (z : RootLattice L)
    (hb : b ∉ u) (hzb : z b = 0) :
    actWord (deleteEdge G a b) u z = actWord G u z := by
  induction u with
  | nil => simp
  | cons i u ih =>
      have hbi : b ≠ i := by
        intro h
        apply hb
        simp [h]
      have hbU : b ∉ u := by
        intro h
        exact hb (List.mem_cons_of_mem i h)
      rw [actWord_cons, actWord_cons, ih hbU]
      apply simpleReflection_deleteEdge_eq_of_ne_of_coord_eq_zero
        G a b i (actWord G u z) hbi.symm
      rw [actWord_apply_of_not_mem G u z hbU, hzb]

/-- Regardless of the deleted edge, a prefix containing no `b` preserves
the `b`-coordinate.  This is the coordinate used in the `c > 0` branch of
the manuscript's deletion argument. -/
theorem actWord_deleteEdge_apply_of_not_mem
    {L : Type uL} [Fintype L]
    (G : SimpleGraph L) (a b : L) (u : List L) (z : RootLattice L)
    (hb : b ∉ u) :
    actWord (deleteEdge G a b) u z b = z b :=
  actWord_apply_of_not_mem (deleteEdge G a b) u z hb

theorem deleteEdge_comm {L : Type uL}
    (G : SimpleGraph L) (a b : L) :
    deleteEdge G a b = deleteEdge G b a := by
  simp [deleteEdge, Sym2.eq_swap]

/-- Coordinate core of the paper's split `Q = u ++ v` argument.  Assume
`u` contains no `b`, `v` contains no `a`, and the initial vector has zero
`a`-coordinate.  Then the action of `v` is unchanged by deleting `a-b`.
Writing `gamma` for that common action, the full deleted-edge action agrees
with the original one if `gamma_b = 0`; in all cases its `b`-coordinate is
exactly `gamma_b`.

The remaining step in the manuscript uses real-root sign coherence: if
`gamma_b > 0`, a real root with this positive coordinate cannot be negative.
That sign theorem is intentionally not assumed here. -/
theorem actWord_deleteEdge_split
    {L : Type uL} [Fintype L]
    (G : SimpleGraph L) (a b : L) (u v : List L) (z : RootLattice L)
    (hbU : b ∉ u) (haV : a ∉ v) (hza : z a = 0) :
    let gamma := actWord G v z
    actWord (deleteEdge G a b) v z = gamma ∧
      (gamma b = 0 →
        actWord (deleteEdge G a b) (u ++ v) z =
          actWord G (u ++ v) z) ∧
      actWord (deleteEdge G a b) (u ++ v) z b = gamma b := by
  let gamma := actWord G v z
  have hTail : actWord (deleteEdge G a b) v z = gamma := by
    have h := actWord_deleteEdge_eq_of_not_mem_of_coord_eq_zero
      G b a v z haV hza
    rw [deleteEdge_comm G a b]
    simpa only [gamma] using h
  refine ⟨hTail, ?_, ?_⟩
  · intro hGamma
    rw [actWord_append, actWord_append, hTail]
    exact actWord_deleteEdge_eq_of_not_mem_of_coord_eq_zero
      G a b u gamma hbU hGamma
  · rw [actWord_append, hTail]
    exact actWord_deleteEdge_apply_of_not_mem G a b u gamma hbU

/-! ## The separated-occurrence cut -/

/-- Every occurrence of `a` lies strictly before every occurrence of `b` in
the finite word `Q`. -/
def AllOccurrencesBefore {L : Type uL}
    (Q : List L) (a b : L) : Prop :=
  ∀ x y : Fin Q.length, Q.get x = a → Q.get y = b → x < y

/-- A separated pair admits the exact cut used in the edge-deletion proof:
`Q = u ++ v`, with no `b` in `u` and no `a` in `v`. -/
theorem exists_append_not_mem_of_allOccurrencesBefore
    {L : Type uL} {Q : List L} {a b : L}
    (hBefore : AllOccurrencesBefore Q a b) :
    ∃ u v : List L, Q = u ++ v ∧ b ∉ u ∧ a ∉ v := by
  classical
  by_cases hb : b ∈ Q
  · let P : ℕ → Prop := fun n ↦ ∃ hn : n < Q.length, Q[n] = b
    have hP : ∃ n, P n := by
      obtain ⟨n, hn, hnb⟩ := (List.mem_iff_getElem.mp hb)
      exact ⟨n, hn, hnb⟩
    let n : ℕ := Nat.find hP
    have hnP : P n := Nat.find_spec hP
    obtain ⟨hnQ, hnLabel⟩ := hnP
    refine ⟨Q.take n, Q.drop n, (Q.take_append_drop n).symm, ?_, ?_⟩
    · intro hbTake
      obtain ⟨i, hiTake, hiLabel⟩ := List.mem_iff_getElem.mp hbTake
      have hiN : i < n :=
        hiTake.trans_le (List.length_take_le n Q)
      have hiQ : i < Q.length := hiN.trans hnQ
      have hiLabelQ : Q[i] = b := by
        simpa only [List.getElem_take] using hiLabel
      have hMin : n ≤ i := Nat.find_min' hP ⟨hiQ, hiLabelQ⟩
      omega
    · intro haDrop
      obtain ⟨j, hjDrop, hjLabel⟩ := List.mem_iff_getElem.mp haDrop
      have hnjQ : n + j < Q.length := by
        simp only [List.length_drop] at hjDrop
        omega
      have hnjLabel : Q[n + j] = a := by
        simpa only [List.getElem_drop] using hjLabel
      have hlt := hBefore ⟨n + j, hnjQ⟩ ⟨n, hnQ⟩ hnjLabel hnLabel
      exact (not_lt_of_ge (by omega : n ≤ n + j)) hlt
  · refine ⟨Q, [], by simp, hb, by simp⟩

/-! ## Iterating finitely many separated edge deletions -/

/-- One graph step deletes a present edge whose two labels are separated in
the fixed word (in one of the two possible orientations). -/
def IsSeparatedEdgeDeletion {L : Type uL} (Q : List L)
    (G H : SimpleGraph L) : Prop :=
  ∃ a b : L, G.Adj a b ∧ H = deleteEdge G a b ∧
    (AllOccurrencesBefore Q a b ∨ AllOccurrencesBefore Q b a)

/-- A finite chain of separated one-edge deletions. -/
abbrev SeparatedEdgeDeletionChain {L : Type uL} (Q : List L)
    (G H : SimpleGraph L) : Prop :=
  Relation.ReflTransGen (IsSeparatedEdgeDeletion Q) G H

/-- Once the one-edge lemma is available, it iterates along every finite
separated deletion chain. -/
theorem isReduced_of_separatedEdgeDeletionChain
    {L : Type uL} (Q : List L)
    (oneEdge : ∀ (G : SimpleGraph L) (a b : L),
      G.Adj a b →
      (AllOccurrencesBefore Q a b ∨ AllOccurrencesBefore Q b a) →
      IsReduced G Q → IsReduced (deleteEdge G a b) Q)
    {G H : SimpleGraph L}
    (hChain : SeparatedEdgeDeletionChain Q G H)
    (hReduced : IsReduced G Q) :
    IsReduced H Q := by
  induction hChain with
  | refl => exact hReduced
  | tail hChain hStep ih =>
      obtain ⟨a, b, hab, rfl, hSeparated⟩ := hStep
      exact oneEdge _ a b hab hSeparated ih

/-- If `H` is a spanning subgraph of the finite graph `G` and every deleted
edge has separated endpoint occurrences in `Q`, then `H` is reached from
`G` by a finite chain of such one-edge deletions. -/
theorem exists_separatedEdgeDeletionChain_of_le
    {L : Type uL} [Fintype L] (Q : List L)
    {G H : SimpleGraph L} (hHG : H ≤ G)
    (hSeparated : ∀ a b : L, G.Adj a b → ¬ H.Adj a b →
      AllOccurrencesBefore Q a b ∨ AllOccurrencesBefore Q b a) :
    SeparatedEdgeDeletionChain Q G H := by
  classical
  let P : ℕ → Prop := fun n ↦
    ∀ K : SimpleGraph L, K.edgeFinset.card = n → H ≤ K →
      (∀ a b : L, K.Adj a b → ¬ H.Adj a b →
        AllOccurrencesBefore Q a b ∨ AllOccurrencesBefore Q b a) →
      SeparatedEdgeDeletionChain Q K H
  have hP : ∀ n, P n := by
    intro n
    refine Nat.strong_induction_on (p := P) n ?_
    intro n ih K hCard hHK hSep
    by_cases hKH : K ≤ H
    · have hEq : K = H := le_antisymm hKH hHK
      subst K
      exact Relation.ReflTransGen.refl
    · change ¬ (∀ a b : L, K.Adj a b → H.Adj a b) at hKH
      push Not at hKH
      obtain ⟨a, b, hKab, hHab⟩ := hKH
      let K' := deleteEdge K a b
      have hHK' : H ≤ K' := by
        intro i j hHij
        apply (deleteEdge_adj K a b i j).2
        refine ⟨hHK hHij, ?_⟩
        intro hEdge
        rcases Sym2.eq_iff.mp hEdge with hij | hij
        · exact hHab (by simpa only [hij.1, hij.2] using hHij)
        · have hHba : H.Adj b a := by
            simpa only [hij.1, hij.2] using hHij
          exact hHab (H.symm.symm b a hHba)
      have hK'K : K' < K := by
        apply (SimpleGraph.deleteEdges_le {s(a, b)}).lt_of_ne
        intro hEq
        change deleteEdge K a b = K at hEq
        have hDeleted : K'.Adj a b := by
          change (deleteEdge K a b).Adj a b
          rw [hEq]
          exact hKab
        exact (deleteEdge_adj K a b a b).1 hDeleted |>.2 rfl
      have hCardLt : K'.edgeFinset.card < n := by
        rw [← hCard]
        exact Finset.card_lt_card
          ((SimpleGraph.edgeFinset_ssubset_edgeFinset).2 hK'K)
      have hSep' : ∀ i j : L, K'.Adj i j → ¬ H.Adj i j →
          AllOccurrencesBefore Q i j ∨ AllOccurrencesBefore Q j i := by
        intro i j hK'ij hHij
        exact hSep i j ((SimpleGraph.deleteEdges_le {s(a, b)}) hK'ij) hHij
      have hTail : SeparatedEdgeDeletionChain Q K' H :=
        ih K'.edgeFinset.card hCardLt K' rfl hHK' hSep'
      exact Relation.ReflTransGen.head
        ⟨a, b, hKab, rfl, hSep a b hKab hHab⟩ hTail
  exact hP G.edgeFinset.card G rfl hHG hSeparated

/-- Finite all-at-once form: reducedness descends from `G` to a spanning
subgraph `H` once every removed edge is separated and the one-edge theorem
is known. -/
theorem isReduced_subgraph_of_all_extra_edges_separated
    {L : Type uL} [Fintype L] (Q : List L)
    {G H : SimpleGraph L} (hHG : H ≤ G)
    (hSeparated : ∀ a b : L, G.Adj a b → ¬ H.Adj a b →
      AllOccurrencesBefore Q a b ∨ AllOccurrencesBefore Q b a)
    (oneEdge : ∀ (K : SimpleGraph L) (a b : L),
      K.Adj a b →
      (AllOccurrencesBefore Q a b ∨ AllOccurrencesBefore Q b a) →
      IsReduced K Q → IsReduced (deleteEdge K a b) Q)
    (hReduced : IsReduced G Q) :
    IsReduced H Q :=
  isReduced_of_separatedEdgeDeletionChain Q oneEdge
    (exists_separatedEdgeDeletionChain_of_le Q hHG hSeparated) hReduced

end QuotientSubmoduleEquidistribution.RepresentationDirected.SegmentReducedness
