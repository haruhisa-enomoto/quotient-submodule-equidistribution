import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Finite.Range
import OpConjecture.RepresentationDirected.ARWordCombinatorics

/-!
# Selected consecutive segments in a finite labelled word

This file formalizes the finite-word content of
`lem:directed-segment-windows`.  No representation-theoretic example or
classification enters this file.
-/

noncomputable section

namespace OpConjecture.RepresentationDirected.ARWord.SelectedSegments

universe u

variable {L : Type u}

/-- The increasing embedding of the selected-word positions into the
positions of the original word. -/
def originalPosition {Q : List L}
    (C : Finset (Fin Q.length)) : Fin C.card ↪o Fin Q.length :=
  C.orderEmbOfFin rfl

@[simp] theorem originalPosition_mem {Q : List L}
    (C : Finset (Fin Q.length)) (x : Fin C.card) :
    originalPosition C x ∈ C :=
  C.orderEmbOfFin_mem rfl x

theorem originalPosition_lt_iff {Q : List L}
    (C : Finset (Fin Q.length)) (x y : Fin C.card) :
    originalPosition C x < originalPosition C y ↔ x < y :=
  (originalPosition C).lt_iff_lt

/-- Every selected original position has a unique position in the selected
word. -/
def selectedIndex {Q : List L} (C : Finset (Fin Q.length))
    (x : Fin Q.length) (hx : x ∈ C) : Fin C.card :=
  (C.orderIsoOfFin rfl).symm ⟨x, hx⟩

@[simp] theorem originalPosition_selectedIndex {Q : List L}
    (C : Finset (Fin Q.length)) (x : Fin Q.length) (hx : x ∈ C) :
    originalPosition C (selectedIndex C x hx) = x := by
  exact congrArg Subtype.val ((C.orderIsoOfFin rfl).apply_symm_apply ⟨x, hx⟩)

@[simp] theorem selectedIndex_originalPosition {Q : List L}
    (C : Finset (Fin Q.length)) (x : Fin C.card) :
    selectedIndex C (originalPosition C x) (originalPosition_mem C x) = x := by
  exact (C.orderIsoOfFin rfl).symm_apply_apply x

/-- The set of omitted occurrences of the label of `x` which precede `x`.
This set, together with the original label, is a canonical name for the
selected consecutive segment containing `x`. -/
def omittedPrefix {Q : List L} (C : Finset (Fin Q.length))
    (x : Fin Q.length) : Set (Fin Q.length) :=
  {z | z < x ∧ ARWord.label Q z = ARWord.label Q x ∧ z ∉ C}

/-- A raw key for a selected segment.  The exact segment type below retains
only keys which are realized by selected positions. -/
abbrev SegmentKey (Q : List L) := L × Set (Fin Q.length)

def segmentKeyAt {Q : List L} (C : Finset (Fin Q.length))
    (x : Fin Q.length) : SegmentKey Q :=
  (ARWord.label Q x, omittedPrefix C x)

/-- The finite set of segment keys actually realized by the selection. -/
def realizedSegmentKeys (Q : List L) (C : Finset (Fin Q.length)) :
    Set (SegmentKey Q) :=
  Set.range fun x : Fin C.card ↦ segmentKeyAt C (originalPosition C x)

/-- Exact selected-segment labels.  This subtype has one point for every
maximal consecutive selected segment and no unused isolated points. -/
abbrev SegmentLabel (Q : List L) (C : Finset (Fin Q.length)) :=
  {A : SegmentKey Q // A ∈ realizedSegmentKeys Q C}

noncomputable instance segmentLabelFintype (Q : List L)
    (C : Finset (Fin Q.length)) : Fintype (SegmentLabel Q C) :=
  (Set.finite_range
    (fun x : Fin C.card ↦ segmentKeyAt C (originalPosition C x))).fintype

/-- Projection of an exact segment label back to its original label. -/
def projectLabel {Q : List L} {C : Finset (Fin Q.length)} :
    SegmentLabel Q C → L := fun A ↦ A.1.1

/-- The selected subword, relabelled by its maximal selected consecutive
segments. -/
def segmentWord (Q : List L) (C : Finset (Fin Q.length)) :
    List (SegmentLabel Q C) :=
  List.ofFn fun x : Fin C.card ↦
    ⟨segmentKeyAt C (originalPosition C x), ⟨x, rfl⟩⟩

/-- The same selected word with its original labels. -/
def selectedWord (Q : List L) (C : Finset (Fin Q.length)) : List L :=
  List.ofFn fun x : Fin C.card ↦ ARWord.label Q (originalPosition C x)

/-- Projecting segment labels recovers the selected subword with its original
labels. -/
@[simp] theorem map_projectLabel_segmentWord (Q : List L)
    (C : Finset (Fin Q.length)) :
    (segmentWord Q C).map projectLabel = selectedWord Q C := by
  simp [segmentWord, selectedWord, projectLabel, segmentKeyAt,
    Function.comp_def]

@[simp] theorem segmentWord_length (Q : List L)
    (C : Finset (Fin Q.length)) :
    (segmentWord Q C).length = C.card := by
  simp [segmentWord]

/-- Regard a position of the literal segment word as a selected position of
the original word. -/
def positionInOriginal (Q : List L) (C : Finset (Fin Q.length))
    (x : Fin (segmentWord Q C).length) : Fin Q.length :=
  originalPosition C (Fin.cast (segmentWord_length Q C) x)

@[simp] theorem positionInOriginal_mem (Q : List L)
    (C : Finset (Fin Q.length))
    (x : Fin (segmentWord Q C).length) :
    positionInOriginal Q C x ∈ C := by
  exact originalPosition_mem C _

theorem positionInOriginal_lt_iff (Q : List L)
    (C : Finset (Fin Q.length))
    (x y : Fin (segmentWord Q C).length) :
    positionInOriginal Q C x < positionInOriginal Q C y ↔ x < y := by
  rw [positionInOriginal, positionInOriginal, originalPosition_lt_iff]
  simp

@[simp] theorem val_label_segmentWord (Q : List L)
    (C : Finset (Fin Q.length))
    (x : Fin (segmentWord Q C).length) :
    (ARWord.label (segmentWord Q C) x).1 =
      segmentKeyAt C (positionInOriginal Q C x) := by
  simp only [ARWord.label, segmentWord, List.get_ofFn, positionInOriginal]

@[simp] theorem projectLabel_label_segmentWord (Q : List L)
    (C : Finset (Fin Q.length))
    (x : Fin (segmentWord Q C).length) :
    projectLabel (ARWord.label (segmentWord Q C) x) =
      ARWord.label Q (positionInOriginal Q C x) := by
  change (ARWord.label (segmentWord Q C) x).1.1 = _
  rw [val_label_segmentWord]
  rfl

/-- The literal segment-word position occupied by a selected original
position. -/
def positionOfSelected (Q : List L) (C : Finset (Fin Q.length))
    (x : Fin Q.length) (hx : x ∈ C) :
    Fin (segmentWord Q C).length :=
  Fin.cast (segmentWord_length Q C).symm (selectedIndex C x hx)

@[simp] theorem positionInOriginal_positionOfSelected (Q : List L)
    (C : Finset (Fin Q.length)) (x : Fin Q.length) (hx : x ∈ C) :
    positionInOriginal Q C (positionOfSelected Q C x hx) = x := by
  simp [positionInOriginal, positionOfSelected]

@[simp] theorem positionOfSelected_positionInOriginal (Q : List L)
    (C : Finset (Fin Q.length))
    (x : Fin (segmentWord Q C).length) :
    positionOfSelected Q C (positionInOriginal Q C x)
      (positionInOriginal_mem Q C x) = x := by
  apply Fin.eq_of_val_eq
  simp [positionOfSelected, positionInOriginal]

theorem positionOfSelected_lt_iff (Q : List L)
    (C : Finset (Fin Q.length))
    {x y : Fin Q.length} (hx : x ∈ C) (_hy : y ∈ C) :
    positionOfSelected Q C x hx < positionOfSelected Q C y _hy ↔ x < y := by
  rw [← positionInOriginal_lt_iff Q C]
  simp

@[simp] theorem val_label_segmentWord_positionOfSelected (Q : List L)
    (C : Finset (Fin Q.length)) (x : Fin Q.length) (hx : x ∈ C) :
    (ARWord.label (segmentWord Q C)
      (positionOfSelected Q C x hx)).1 = segmentKeyAt C x := by
  rw [val_label_segmentWord, positionInOriginal_positionOfSelected]

/-- Oriented equality criterion for canonical segment labels. -/
theorem segmentKeyAt_eq_iff_of_lt {Q : List L}
    (C : Finset (Fin Q.length)) {x y : Fin Q.length}
    (hx : x ∈ C) (_hy : y ∈ C) (hxy : x < y) :
    segmentKeyAt C x = segmentKeyAt C y ↔
      ARWord.label Q x = ARWord.label Q y ∧
        ∀ z : Fin Q.length, x < z → z < y →
          ARWord.label Q z = ARWord.label Q x → z ∈ C := by
  constructor
  · intro h
    have hlabel : ARWord.label Q x = ARWord.label Q y :=
      congrArg Prod.fst h
    refine ⟨hlabel, ?_⟩
    intro z hxz hzy hzlabel
    by_contra hzC
    have hzyPrefix : z ∈ omittedPrefix C y := by
      exact ⟨hzy, hzlabel.trans hlabel, hzC⟩
    have hzxPrefix : z ∈ omittedPrefix C x := by
      simpa [segmentKeyAt] using
        congrArg (fun t : SegmentKey Q ↦ z ∈ t.2) h.symm ▸ hzyPrefix
    exact (not_lt_of_ge (le_of_lt hxz)) hzxPrefix.1
  · rintro ⟨hlabel, hall⟩
    apply Prod.ext hlabel
    ext z
    constructor
    · rintro ⟨hzx, hzlabel, hzC⟩
      exact ⟨hzx.trans hxy, hzlabel.trans hlabel, hzC⟩
    · rintro ⟨hzy, hzlabel, hzC⟩
      have hzlabelX : ARWord.label Q z = ARWord.label Q x :=
        hzlabel.trans hlabel.symm
      rcases lt_trichotomy z x with hzx | hzx | hxz
      · exact ⟨hzx, hzlabelX, hzC⟩
      · subst z
        exact False.elim (hzC hx)
      · exact False.elim (hzC (hall z hxz hzy hzlabelX))

/-- An omitted occurrence to the right of one point in a segment lies to the
right of every selected point in that segment. -/
theorem sameSegment_lt_omitted_right {Q : List L}
    (C : Finset (Fin Q.length)) {x u q : Fin Q.length}
    (_hx : x ∈ C) (hu : u ∈ C)
    (hxu : segmentKeyAt C x = segmentKeyAt C u)
    (hxq : x < q) (hqLabel : ARWord.label Q q = ARWord.label Q x)
    (hqC : q ∉ C) :
    u < q := by
  have hlabel : ARWord.label Q x = ARWord.label Q u :=
    congrArg Prod.fst hxu
  have hprefix : omittedPrefix C x = omittedPrefix C u :=
    congrArg Prod.snd hxu
  rcases lt_trichotomy u q with huq | huq | hqu
  · exact huq
  · subst q
    exact False.elim (hqC hu)
  · have hqU : q ∈ omittedPrefix C u :=
      ⟨hqu, hqLabel.trans hlabel, hqC⟩
    have hqX : q ∈ omittedPrefix C x := by
      rw [hprefix]
      exact hqU
    exact False.elim ((not_lt_of_ge (le_of_lt hxq)) hqX.1)

/-- Dually, an omitted occurrence to the left of one selected point in a
segment lies to the left of every selected point in that segment. -/
theorem omitted_left_lt_sameSegment {Q : List L}
    (C : Finset (Fin Q.length)) {x u q : Fin Q.length}
    (_hx : x ∈ C) (hu : u ∈ C)
    (hxu : segmentKeyAt C x = segmentKeyAt C u)
    (hqx : q < x) (hqLabel : ARWord.label Q q = ARWord.label Q x)
    (hqC : q ∉ C) :
    q < u := by
  have hprefix : omittedPrefix C x = omittedPrefix C u :=
    congrArg Prod.snd hxu
  rcases lt_trichotomy q u with hqu | hqu | huq
  · exact hqu
  · subst q
    exact False.elim (hqC hu)
  · have hqX : q ∈ omittedPrefix C x :=
      ⟨hqx, hqLabel, hqC⟩
    have hqU : q ∈ omittedPrefix C u := by
      rw [← hprefix]
      exact hqX
    exact False.elim ((not_lt_of_ge (le_of_lt huq)) hqU.1)

/-- Different segment labels on selected occurrences of the same original
label are separated by an omitted occurrence of that label. -/
theorem exists_omitted_between_of_segmentKeyAt_ne {Q : List L}
    (C : Finset (Fin Q.length)) {x y : Fin Q.length}
    (hx : x ∈ C) (hy : y ∈ C) (hxy : x < y)
    (hlabel : ARWord.label Q x = ARWord.label Q y)
    (hne : segmentKeyAt C x ≠ segmentKeyAt C y) :
    ∃ q : Fin Q.length, x < q ∧ q < y ∧
      ARWord.label Q q = ARWord.label Q x ∧ q ∉ C := by
  classical
  by_contra hExists
  apply hne
  apply (segmentKeyAt_eq_iff_of_lt C hx hy hxy).2
  refine ⟨hlabel, ?_⟩
  intro q hxq hqy hqLabel
  by_contra hqC
  exact hExists ⟨q, hxq, hqy, hqLabel, hqC⟩

/-- Immediate predecessors in the selected segment word are exactly the
selected immediate predecessors in the original word. -/
theorem isPrevious_segmentWord_iff
    {Q : List L} (C : Finset (Fin Q.length))
    (p x : Fin (segmentWord Q C).length) :
    ARWord.IsPrevious (segmentWord Q C) p x ↔
      ARWord.IsPrevious Q
        (positionInOriginal Q C p) (positionInOriginal Q C x) := by
  let op := positionInOriginal Q C p
  let ox := positionInOriginal Q C x
  have hpC : op ∈ C := positionInOriginal_mem Q C p
  have hxC : ox ∈ C := positionInOriginal_mem Q C x
  constructor
  · rintro ⟨hpx, hkey, hnone⟩
    have hOpOx : op < ox := (positionInOriginal_lt_iff Q C p x).2 hpx
    have hkey' : segmentKeyAt C op = segmentKeyAt C ox := by
      simpa only [val_label_segmentWord] using congrArg Subtype.val hkey
    have hsegment :=
      (segmentKeyAt_eq_iff_of_lt C hpC hxC hOpOx).1 hkey'
    refine ⟨hOpOx, hsegment.1, ?_⟩
    intro z hOpZ hZOx hzLabel
    have hzC : z ∈ C :=
      hsegment.2 z hOpZ hZOx (hzLabel.trans hsegment.1.symm)
    let zi := positionOfSelected Q C z hzC
    have hpzi : p < zi := by
      apply (positionInOriginal_lt_iff Q C p zi).1
      simpa only [zi, positionInOriginal_positionOfSelected] using hOpZ
    have hzix : zi < x := by
      apply (positionInOriginal_lt_iff Q C zi x).1
      simpa only [zi, positionInOriginal_positionOfSelected] using hZOx
    have hOpZKey : segmentKeyAt C op = segmentKeyAt C z := by
      apply (segmentKeyAt_eq_iff_of_lt C hpC hzC hOpZ).2
      refine ⟨hsegment.1.trans hzLabel.symm, ?_⟩
      intro w hOpW hWZ hwLabel
      exact hsegment.2 w hOpW (hWZ.trans hZOx)
        hwLabel
    apply hnone zi hpzi hzix
    apply Subtype.ext
    rw [val_label_segmentWord_positionOfSelected, val_label_segmentWord]
    exact hOpZKey.symm.trans hkey'
  · rintro ⟨hOpOx, hlabel, hnone⟩
    have hpx : p < x := (positionInOriginal_lt_iff Q C p x).1 hOpOx
    refine ⟨hpx, ?_, ?_⟩
    · apply Subtype.ext
      rw [val_label_segmentWord, val_label_segmentWord]
      apply (segmentKeyAt_eq_iff_of_lt C hpC hxC hOpOx).2
      refine ⟨hlabel, ?_⟩
      intro z hOpZ hZOx hzLabel
      exact False.elim (hnone z hOpZ hZOx (hzLabel.trans hlabel))
    · intro z hpz hzx hzKey
      apply hnone (positionInOriginal Q C z)
      · exact (positionInOriginal_lt_iff Q C p z).2 hpz
      · exact (positionInOriginal_lt_iff Q C z x).2 hzx
      · have := congrArg projectLabel hzKey
        simpa only [projectLabel_label_segmentWord] using this

/-- A segment predecessor exists exactly when the original predecessor is
selected. -/
theorem exists_isPrevious_segmentWord_iff
    {Q : List L} (C : Finset (Fin Q.length))
    (x : Fin (segmentWord Q C).length) :
    (∃ p : Fin (segmentWord Q C).length,
        ARWord.IsPrevious (segmentWord Q C) p x) ↔
      ∃ p : Fin Q.length,
        ARWord.IsPrevious Q p (positionInOriginal Q C x) ∧ p ∈ C := by
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨positionInOriginal Q C p,
      (isPrevious_segmentWord_iff C p x).1 hp,
      positionInOriginal_mem Q C p⟩
  · rintro ⟨p, hp, hpC⟩
    let ps := positionOfSelected Q C p hpC
    refine ⟨ps, (isPrevious_segmentWord_iff C ps x).2 ?_⟩
    simpa only [ps, positionInOriginal_positionOfSelected] using hp

/-- When the two predecessors exist, their positions agree under the
selected-position embedding. -/
theorem isPrevious_segmentWord_agrees
    {Q : List L} (C : Finset (Fin Q.length))
    {ps x : Fin (segmentWord Q C).length} {p : Fin Q.length}
    (hps : ARWord.IsPrevious (segmentWord Q C) ps x)
    (hp : ARWord.IsPrevious Q p (positionInOriginal Q C x)) :
    positionInOriginal Q C ps = p :=
  ARWord.isPrevious_unique (isPrevious_segmentWord_iff C ps x |>.1 hps) hp

/-- Two selected segments are joined when an original middle arrow has one
endpoint in each segment.  This is the finite-word version of the
manuscript's graph whose edges are the AR arrows joining selected segments. -/
def segmentGraph (G : SimpleGraph L) (Q : List L)
    (C : Finset (Fin Q.length)) : SimpleGraph (SegmentLabel Q C) where
  Adj A B :=
    ∃ y x : Fin (segmentWord Q C).length,
      ARWord.label (segmentWord Q C) y = A ∧
        ARWord.label (segmentWord Q C) x = B ∧
          (ARWord.IsMiddle G Q
              (positionInOriginal Q C y) (positionInOriginal Q C x) ∨
            ARWord.IsMiddle G Q
              (positionInOriginal Q C x) (positionInOriginal Q C y))
  symm := by
    constructor
    rintro A B ⟨y, x, hy, hx, hmiddle⟩
    exact ⟨x, y, hx, hy, hmiddle.elim Or.inr Or.inl⟩
  loopless := by
    constructor
    rintro A ⟨y, x, hy, hx, hmiddle⟩
    have hkey :
        segmentKeyAt C (positionInOriginal Q C y) =
          segmentKeyAt C (positionInOriginal Q C x) := by
      simpa only [val_label_segmentWord] using
        congrArg Subtype.val (hy.trans hx.symm)
    have hlabel :
        ARWord.label Q (positionInOriginal Q C y) =
          ARWord.label Q (positionInOriginal Q C x) :=
      congrArg Prod.fst hkey
    exact hmiddle.elim
      (fun h ↦ h.1.ne hlabel)
      (fun h ↦ h.1.ne hlabel.symm)

/-- Segment adjacency always projects to adjacency of the corresponding
original labels. -/
theorem segmentGraph_adj_projectLabel
    {G : SimpleGraph L} {Q : List L} {C : Finset (Fin Q.length)}
    {A B : SegmentLabel Q C}
    (hAB : (segmentGraph G Q C).Adj A B) :
    G.Adj (projectLabel A) (projectLabel B) := by
  obtain ⟨y, x, hy, hx, hmiddle⟩ := hAB
  have hyLabel :
      ARWord.label Q (positionInOriginal Q C y) = projectLabel A := by
    have := congrArg projectLabel hy
    simpa only [projectLabel_label_segmentWord] using this
  have hxLabel :
      ARWord.label Q (positionInOriginal Q C x) = projectLabel B := by
    have := congrArg projectLabel hx
    simpa only [projectLabel_label_segmentWord] using this
  rcases hmiddle with hmiddle | hmiddle
  · simpa only [hyLabel, hxLabel] using hmiddle.1
  · simpa only [hyLabel, hxLabel] using hmiddle.1.symm

/-- Every selected original middle position remains a middle position after
relabeling by segments. -/
theorem isMiddle_segmentWord_of_isMiddle
    {G : SimpleGraph L} {Q : List L} (C : Finset (Fin Q.length))
    {y x : Fin (segmentWord Q C).length}
    (hMiddle : ARWord.IsMiddle G Q
      (positionInOriginal Q C y) (positionInOriginal Q C x)) :
    ARWord.IsMiddle (segmentGraph G Q C) (segmentWord Q C) y x := by
  refine ⟨⟨y, x, rfl, rfl, Or.inl hMiddle⟩,
    (positionInOriginal_lt_iff Q C y x).1 hMiddle.2.1, ?_, ?_⟩
  · intro p hp
    apply (positionInOriginal_lt_iff Q C p y).1
    exact hMiddle.2.2.1 (positionInOriginal Q C p)
      ((isPrevious_segmentWord_iff C p x).1 hp)
  · intro z hyz hzx hzLabel
    apply hMiddle.2.2.2 (positionInOriginal Q C z)
      ((positionInOriginal_lt_iff Q C y z).2 hyz)
      ((positionInOriginal_lt_iff Q C z x).2 hzx)
    have := congrArg projectLabel hzLabel
    simpa only [projectLabel_label_segmentWord] using this

/-- Exact selected-window theorem.  For the natural segment graph, a
segment-word middle position is exactly a selected original middle position. -/
theorem isMiddle_segmentWord_iff
    {G : SimpleGraph L} {Q : List L}
    (hRuns : ARWord.HasOnlyBoundaryRepeatedRuns G Q)
    (C : Finset (Fin Q.length))
    (y x : Fin (segmentWord Q C).length) :
    ARWord.IsMiddle (segmentGraph G Q C) (segmentWord Q C) y x ↔
      ARWord.IsMiddle G Q
        (positionInOriginal Q C y) (positionInOriginal Q C x) := by
  let oy := positionInOriginal Q C y
  let ox := positionInOriginal Q C x
  have hyC : oy ∈ C := positionInOriginal_mem Q C y
  have hxC : ox ∈ C := positionInOriginal_mem Q C x
  constructor
  · rintro ⟨hAdj, hyx, hBefore, hLast⟩
    have hOyOx : oy < ox := (positionInOriginal_lt_iff Q C y x).2 hyx
    have hAdjOrig : G.Adj (ARWord.label Q oy) (ARWord.label Q ox) := by
      simpa only [projectLabel_label_segmentWord] using
        (segmentGraph_adj_projectLabel hAdj)
    obtain ⟨u, v, hu, hv, hUV⟩ := hAdj
    let ou := positionInOriginal Q C u
    let ov := positionInOriginal Q C v
    have huC : ou ∈ C := positionInOriginal_mem Q C u
    have hvC : ov ∈ C := positionInOriginal_mem Q C v
    have hUKey : segmentKeyAt C ou = segmentKeyAt C oy := by
      simpa only [val_label_segmentWord] using congrArg Subtype.val hu
    have hVKey : segmentKeyAt C ov = segmentKeyAt C ox := by
      simpa only [val_label_segmentWord] using congrArg Subtype.val hv
    have hULabel : ARWord.label Q ou = ARWord.label Q oy :=
      congrArg Prod.fst hUKey
    have hVLabel : ARWord.label Q ov = ARWord.label Q ox :=
      congrArg Prod.fst hVKey
    have hPredBefore :
        ∀ p : Fin Q.length, ARWord.IsPrevious Q p ox → p < oy := by
      intro p hp
      by_contra hpOy
      have hOyNeP : oy ≠ p := by
        intro hEq
        subst p
        exact hAdjOrig.ne hp.2.1
      have hOyP : oy < p :=
        lt_of_le_of_ne (le_of_not_gt hpOy) hOyNeP
      have hpNotC : p ∉ C := by
        intro hpC
        let ps := positionOfSelected Q C p hpC
        have hpSegment :
            ARWord.IsPrevious (segmentWord Q C) ps x := by
          apply (isPrevious_segmentWord_iff C ps x).2
          simpa only [ps, positionInOriginal_positionOfSelected] using hp
        have hpsY := hBefore ps hpSegment
        have hpOy' : p < oy := by
          have h := (positionInOriginal_lt_iff Q C ps y).2 hpsY
          simpa only [ps, oy, positionInOriginal_positionOfSelected] using h
        exact (not_lt_of_ge (le_of_lt hOyP)) hpOy'
      have hpOv : p < ov := by
        apply omitted_left_lt_sameSegment C hxC hvC hVKey.symm
          hp.1 hp.2.1 hpNotC
      have hpOu : p < ou := by
        rcases hUV with hUVMiddle | hVUMiddle
        · obtain ⟨r, hr⟩ :=
            (ARWord.exists_isPrevious_iff_exists_lt_label_eq).2
              ⟨p, hpOv, hp.2.1.trans hVLabel.symm⟩
          have hpLeR : p ≤ r := by
            by_contra hpR
            have hrp : r < p := lt_of_not_ge hpR
            exact (hr.2.2 p hrp hpOv (hp.2.1.trans hVLabel.symm)).elim
          exact hpLeR.trans_lt (hUVMiddle.2.2.1 r hr)
        · exact hpOv.trans hVUMiddle.2.1
      have hOxOu : ox < ou := by
        rcases lt_trichotomy ou ox with hOuOx | hOuOx | hOxOu
        · have hyu : y < u := by
            apply (positionInOriginal_lt_iff Q C y u).1
            exact hOyP.trans hpOu
          have hux : u < x :=
            (positionInOriginal_lt_iff Q C u x).1 hOuOx
          exact False.elim ((hLast u hyu hux) hu)
        · exact False.elim (hAdjOrig.ne
            (hULabel.symm.trans (congrArg (ARWord.label Q) hOuOx)))
        · exact hOxOu
      have hNoA :
          ∀ q : Fin Q.length, p < q → q < ox →
            ARWord.label Q q ≠ ARWord.label Q oy := by
        intro q hpq hqOx hqLabel
        have hOyOu : oy < ou := hOyP.trans hpOu
        have hUWide :=
          (segmentKeyAt_eq_iff_of_lt C hyC huC hOyOu).1 hUKey.symm
        have hqC : q ∈ C :=
          hUWide.2 q (hOyP.trans hpq) (hqOx.trans hOxOu) hqLabel
        let qi := positionOfSelected Q C q hqC
        have hyqi : y < qi := by
          apply (positionInOriginal_lt_iff Q C y qi).1
          simpa only [qi, positionInOriginal_positionOfSelected] using
            hOyP.trans hpq
        have hqix : qi < x := by
          apply (positionInOriginal_lt_iff Q C qi x).1
          simpa only [qi, positionInOriginal_positionOfSelected] using hqOx
        apply hLast qi hyqi hqix
        apply Subtype.ext
        rw [val_label_segmentWord_positionOfSelected, val_label_segmentWord]
        have hOyQ : oy < q := hOyP.trans hpq
        have hYQKey : segmentKeyAt C oy = segmentKeyAt C q := by
          apply (segmentKeyAt_eq_iff_of_lt C hyC hqC hOyQ).2
          refine ⟨hqLabel.symm, ?_⟩
          intro t hOyT hTQ htLabel
          exact hUWide.2 t hOyT (hTQ.trans (hqOx.trans hOxOu)) htLabel
        exact hYQKey.symm
      exact False.elim (hRuns hAdjOrig.symm
        ⟨p, ox, hp.1, hp.2.1, rfl, hNoA,
          ⟨oy, hOyP, rfl⟩, ⟨ou, hOxOu, hULabel⟩⟩)
    have hLastOrig :
        ∀ z : Fin Q.length, oy < z → z < ox →
          ARWord.label Q z ≠ ARWord.label Q oy := by
      intro z hOyZ hZOx hzLabel
      have hOmitted :
          ∃ q : Fin Q.length, oy < q ∧ q < ox ∧
            ARWord.label Q q = ARWord.label Q oy ∧ q ∉ C := by
        by_cases hzC : z ∈ C
        · let zi := positionOfSelected Q C z hzC
          have hyzi : y < zi := by
            apply (positionInOriginal_lt_iff Q C y zi).1
            simpa only [zi, positionInOriginal_positionOfSelected] using hOyZ
          have hzix : zi < x := by
            apply (positionInOriginal_lt_iff Q C zi x).1
            simpa only [zi, positionInOriginal_positionOfSelected] using hZOx
          have hKeyNe : segmentKeyAt C oy ≠ segmentKeyAt C z := by
            intro hKey
            apply hLast zi hyzi hzix
            apply Subtype.ext
            rw [val_label_segmentWord_positionOfSelected, val_label_segmentWord]
            exact hKey.symm
          obtain ⟨q, hOyQ, hQZ, hqLabel, hqC⟩ :=
            exists_omitted_between_of_segmentKeyAt_ne C hyC hzC hOyZ
              hzLabel.symm hKeyNe
          exact ⟨q, hOyQ, hQZ.trans hZOx, hqLabel, hqC⟩
        · exact ⟨z, hOyZ, hZOx, hzLabel, hzC⟩
      obtain ⟨q, hOyQ, hQOx, hqLabel, hqC⟩ := hOmitted
      have hOuQ : ou < q :=
        sameSegment_lt_omitted_right C hyC huC hUKey.symm
          hOyQ hqLabel hqC
      have hOuLeOy : ou ≤ oy := by
        apply le_of_not_gt
        intro hOyOu
        have hux : u < x := by
          apply (positionInOriginal_lt_iff Q C u x).1
          exact hOuQ.trans hQOx
        have hyu : y < u :=
          (positionInOriginal_lt_iff Q C y u).1 hOyOu
        exact (hLast u hyu hux) hu
      have hOvQ : ov < q := by
        rcases hUV with hUVMiddle | hVUMiddle
        · rcases lt_trichotomy ov q with hOvQ | hOvQ | hQOv
          · exact hOvQ
          · subst q
            exact False.elim
              (hAdjOrig.ne (hqLabel.symm.trans hVLabel))
          · exact False.elim
              (hUVMiddle.2.2.2 q hOuQ hQOv
                (hqLabel.trans hULabel.symm))
        · exact hVUMiddle.2.1.trans (hOuQ)
      have hOvOx : ov < ox := hOvQ.trans hQOx
      have hvx : v < x :=
        (positionInOriginal_lt_iff Q C v x).1 hOvOx
      obtain ⟨r, hr⟩ :=
        (ARWord.exists_isPrevious_iff_exists_lt_label_eq).2
          ⟨v, hvx, hv⟩
      have hrY : r < y := hBefore r hr
      have hvLeR : v ≤ r := by
        by_contra hvR
        have hrv : r < v := lt_of_not_ge hvR
        exact (hr.2.2 v hrv hvx hv).elim
      have hOvOy : ov < oy := by
        apply (positionInOriginal_lt_iff Q C v y).2
        exact hvLeR.trans_lt hrY
      have hVWide :=
        (segmentKeyAt_eq_iff_of_lt C hvC hxC hOvOx).1 hVKey
      have hNoB :
          ∀ t : Fin Q.length, oy < t → t < q →
            ARWord.label Q t ≠ ARWord.label Q ox := by
        intro t hOyT hTQ htLabel
        have htC : t ∈ C :=
          hVWide.2 t (hOvOy.trans hOyT) (hTQ.trans hQOx)
            (htLabel.trans hVLabel.symm)
        let ti := positionOfSelected Q C t htC
        have hrti : r < ti := by
          exact hrY.trans ((positionInOriginal_lt_iff Q C y ti).1 (by
            simpa only [ti, positionInOriginal_positionOfSelected] using hOyT))
        have htix : ti < x := by
          apply (positionInOriginal_lt_iff Q C ti x).1
          simpa only [ti, positionInOriginal_positionOfSelected] using
            hTQ.trans hQOx
        apply hr.2.2 ti hrti htix
        apply Subtype.ext
        rw [val_label_segmentWord_positionOfSelected, val_label_segmentWord]
        have hOvT : ov < t := hOvOy.trans hOyT
        have hVTKey : segmentKeyAt C ov = segmentKeyAt C t := by
          apply (segmentKeyAt_eq_iff_of_lt C hvC htC hOvT).2
          refine ⟨hVLabel.trans htLabel.symm, ?_⟩
          intro s hOvS hST hsLabel
          exact hVWide.2 s hOvS (hST.trans (hTQ.trans hQOx)) hsLabel
        exact hVTKey.symm.trans hVKey
      exact False.elim (hRuns hAdjOrig
        ⟨oy, q, hOyQ, rfl, hqLabel, hNoB,
          ⟨ov, hOvOy, hVLabel⟩, ⟨ox, hQOx, rfl⟩⟩)
    exact ⟨hAdjOrig, hOyOx, hPredBefore, hLastOrig⟩
  · exact isMiddle_segmentWord_of_isMiddle C

/-- Literal equivalence between segment-word middle positions and selected
original middle positions; this is the subtype form of
`mid_C(x) = mid(x) ∩ C`. -/
def middlePositionEquiv
    {G : SimpleGraph L} {Q : List L}
    (hRuns : ARWord.HasOnlyBoundaryRepeatedRuns G Q)
    (C : Finset (Fin Q.length))
    (x : Fin (segmentWord Q C).length) :
    {y : Fin (segmentWord Q C).length //
      ARWord.IsMiddle (segmentGraph G Q C) (segmentWord Q C) y x} ≃
      {y : Fin Q.length //
        ARWord.IsMiddle G Q y (positionInOriginal Q C x) ∧ y ∈ C} where
  toFun y :=
    ⟨positionInOriginal Q C y.1,
      (isMiddle_segmentWord_iff hRuns C y.1 x).1 y.2,
      positionInOriginal_mem Q C y.1⟩
  invFun y :=
    ⟨positionOfSelected Q C y.1 y.2.2,
      (isMiddle_segmentWord_iff hRuns C _ x).2 (by
        simpa only [positionInOriginal_positionOfSelected] using y.2.1)⟩
  left_inv y := by
    apply Subtype.ext
    exact positionOfSelected_positionInOriginal Q C y.1
  right_inv y := by
    apply Subtype.ext
    exact positionInOriginal_positionOfSelected Q C y.1 y.2.2

/-- Relabeling by selected segments preserves the boundary-run property on
the natural segment graph. -/
theorem hasOnlyBoundaryRepeatedRuns_segmentWord
    {G : SimpleGraph L} {Q : List L}
    (hRuns : ARWord.HasOnlyBoundaryRepeatedRuns G Q)
    (C : Finset (Fin Q.length)) :
    ARWord.HasOnlyBoundaryRepeatedRuns
      (segmentGraph G Q C) (segmentWord Q C) := by
  intro A B hAB hbad
  obtain ⟨x, y, hxy, hxA, hyA, hNoB,
      ⟨z, hzx, hzB⟩, ⟨w, hyw, hwB⟩⟩ := hbad
  let ox := positionInOriginal Q C x
  let oy := positionInOriginal Q C y
  let oz := positionInOriginal Q C z
  let ow := positionInOriginal Q C w
  have hxC : ox ∈ C := positionInOriginal_mem Q C x
  have hyC : oy ∈ C := positionInOriginal_mem Q C y
  have hzC : oz ∈ C := positionInOriginal_mem Q C z
  have hwC : ow ∈ C := positionInOriginal_mem Q C w
  have hOxOy : ox < oy := (positionInOriginal_lt_iff Q C x y).2 hxy
  have hOzOx : oz < ox := (positionInOriginal_lt_iff Q C z x).2 hzx
  have hOyOw : oy < ow := (positionInOriginal_lt_iff Q C y w).2 hyw
  have hAKey : segmentKeyAt C ox = segmentKeyAt C oy := by
    simpa only [val_label_segmentWord] using
      congrArg Subtype.val (hxA.trans hyA.symm)
  have hBKey : segmentKeyAt C oz = segmentKeyAt C ow := by
    simpa only [val_label_segmentWord] using
      congrArg Subtype.val (hzB.trans hwB.symm)
  have hALabel : ARWord.label Q ox = projectLabel A := by
    have := congrArg projectLabel hxA
    simpa only [projectLabel_label_segmentWord] using this
  have hBLabel : ARWord.label Q oz = projectLabel B := by
    have := congrArg projectLabel hzB
    simpa only [projectLabel_label_segmentWord] using this
  have hOyLabel : ARWord.label Q oy = projectLabel A := by
    have := congrArg projectLabel hyA
    simpa only [projectLabel_label_segmentWord] using this
  have hOwLabel : ARWord.label Q ow = projectLabel B := by
    have := congrArg projectLabel hwB
    simpa only [projectLabel_label_segmentWord] using this
  apply hRuns (segmentGraph_adj_projectLabel hAB)
  refine ⟨ox, oy, hOxOy, hALabel, hOyLabel, ?_,
    ⟨oz, hOzOx, hBLabel⟩, ⟨ow, hOyOw, hOwLabel⟩⟩
  intro q hOxQ hQOy hqB
  have hOzOw : oz < ow := hOzOx.trans (hOxOy.trans hOyOw)
  have hBWide :=
    (segmentKeyAt_eq_iff_of_lt C hzC hwC hOzOw).1 hBKey
  have hqC : q ∈ C := by
    apply hBWide.2 q
    · exact hOzOx.trans hOxQ
    · exact hQOy.trans hOyOw
    · exact hqB.trans hBLabel.symm
  let qi := positionOfSelected Q C q hqC
  have hxqi : x < qi := by
    apply (positionInOriginal_lt_iff Q C x qi).1
    simpa only [qi, positionInOriginal_positionOfSelected] using hOxQ
  have hqiy : qi < y := by
    apply (positionInOriginal_lt_iff Q C qi y).1
    simpa only [qi, positionInOriginal_positionOfSelected] using hQOy
  apply hNoB qi hxqi hqiy
  have hOzQ : oz < q := hOzOx.trans hOxQ
  have hOzQKey : segmentKeyAt C oz = segmentKeyAt C q := by
    apply (segmentKeyAt_eq_iff_of_lt C hzC hqC hOzQ).2
    refine ⟨hBLabel.trans hqB.symm, ?_⟩
    intro t hOzT hTQ htLabel
    exact hBWide.2 t hOzT (hTQ.trans (hQOy.trans hOyOw)) htLabel
  exact (by
    calc
      ARWord.label (segmentWord Q C) qi =
          ARWord.label (segmentWord Q C) z := by
        apply Subtype.ext
        rw [val_label_segmentWord_positionOfSelected, val_label_segmentWord]
        exact hOzQKey.symm
      _ = B := hzB)

end OpConjecture.RepresentationDirected.ARWord.SelectedSegments
