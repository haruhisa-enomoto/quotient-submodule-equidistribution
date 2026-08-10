import Mathlib.Data.Fin.FlagRange
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fintype.Sort
import QuotientSubmoduleEquidistribution.ConvexGeometry.ClosedSets

/-!
# Maximal closed-set flags and legal deletion chains

This file proves that maximal flags in a finite convex geometry are exactly
saturated one-point deletion chains.  `ClosedFlag` is Mathlib’s genuine
maximal-chain type `Flag`, so maximality is not encoded as an assumption on a
preselected enumeration.
-/

noncomputable section

open Set

namespace QuotientSubmoduleEquidistribution.SetClosure

universe u

variable {E : Type u} [Fintype E]
  {c : SetClosure E}

/-- A maximal chain in the actual poset of closed supports. -/
abbrev ClosedFlag (c : SetClosure E) :=
  Flag c.Closeds

/-- Pure finite-set data for a saturated endpoint deletion chain.

No closure or rejectivity hypothesis is built into this structure.  It
is the input shape needed for the converse direction of the paper:
right rejectivity of the terms will imply their quotient closedness. -/
structure SaturatedSupportDeletionChain (E : Type u)
    [Fintype E] where
  support : Fin (Fintype.card E + 1) → Set E
  removed : Fin (Fintype.card E) → E
  top : support 0 = Set.univ
  bottom : support (Fin.last (Fintype.card E)) = ∅
  removed_mem :
    ∀ i, removed i ∈ support i.castSucc
  step :
    ∀ i, support i.succ =
      support i.castSucc \ {removed i}

/-- A saturated legal deletion chain, read from top to bottom.

There are `|E| + 1` closed supports and `|E|` one-point deletion
steps.  `removed_mem` makes each step strict, rather than allowing a
vacuous repeated deletion. -/
structure LegalDeletionChain (c : SetClosure E) where
  support : Fin (Fintype.card E + 1) → Set E
  closed : ∀ i, c.IsClosed (support i)
  removed : Fin (Fintype.card E) → E
  top : support 0 = Set.univ
  bottom : support (Fin.last (Fintype.card E)) = ∅
  removed_mem :
    ∀ i, removed i ∈ support i.castSucc
  step :
    ∀ i, support i.succ =
      support i.castSucc \ {removed i}

/-- A saturated top-to-bottom chain in any poset order-isomorphic to the
closed-set lattice.

The endpoints are stated through the order isomorphism because the target
poset need not carry chosen `OrderTop` or `OrderBot` instances. -/
structure SaturatedOrderDeletionChain
    {P : Type*} [PartialOrder P]
    (e : c.Closeds ≃o P) where
  term : Fin (Fintype.card E + 1) → P
  top : term 0 = e ⊤
  bottom : term (Fin.last (Fintype.card E)) = e ⊥
  step_covBy :
    ∀ i : Fin (Fintype.card E),
      term i.succ ⋖ term i.castSucc

/-- Forget the closedness certificates of a legal deletion chain. -/
def LegalDeletionChain.toSaturatedSupport
    (d : LegalDeletionChain c) :
    SaturatedSupportDeletionChain E where
  support := d.support
  removed := d.removed
  top := d.top
  bottom := d.bottom
  removed_mem := d.removed_mem
  step := d.step

/-- Add closedness certificates to a pure saturated support chain. -/
def SaturatedSupportDeletionChain.toLegal
    (d : SaturatedSupportDeletionChain E)
    (hclosed : ∀ i, c.IsClosed (d.support i)) :
    LegalDeletionChain c where
  support := d.support
  closed := hclosed
  removed := d.removed
  top := d.top
  bottom := d.bottom
  removed_mem := d.removed_mem
  step := d.step

namespace LegalDeletionChain

/-- Read a deletion chain in the opposite direction as an increasing
chain of actual closed-set lattice elements. -/
def ascending (d : LegalDeletionChain c) :
    Fin (Fintype.card E + 1) → c.Closeds :=
  fun i ↦ ⟨d.support i.rev, d.closed i.rev⟩

@[simp]
theorem coe_ascending (d : LegalDeletionChain c)
    (i : Fin (Fintype.card E + 1)) :
    (d.ascending i : Set E) = d.support i.rev :=
  rfl

theorem ascending_zero
    (d : LegalDeletionChain c)
    (hempty : c.IsClosed ∅) :
    d.ascending 0 = ⊥ := by
  apply Subtype.ext
  simp only [coe_ascending, Fin.rev_zero, d.bottom,
    coe_bot, hempty.closure_eq]

theorem ascending_last
    (d : LegalDeletionChain c) :
    d.ascending (Fin.last (Fintype.card E)) = ⊤ := by
  apply Subtype.ext
  simp only [coe_ascending, Fin.rev_last, d.top, coe_top]

/-- Every reversed deletion step is a cover in the actual closed-set
poset. -/
theorem ascending_covBy
    (d : LegalDeletionChain c)
    (i : Fin (Fintype.card E)) :
    d.ascending i.castSucc ⋖ d.ascending i.succ := by
  let x := d.removed i.rev
  have hsmall :
      d.support i.rev.succ =
        d.support i.rev.castSucc \ {x} :=
    d.step i.rev
  have hx :
      x ∈ d.support i.rev.castSucc :=
    d.removed_mem i.rev
  have hins :
      d.support i.rev.castSucc =
        insert x (d.support i.rev.succ) := by
    rw [hsmall]
    exact (insert_sdiff_self_of_mem hx).symm
  have hxsmall :
      x ∉ d.support i.rev.succ := by
    rw [hsmall]
    simp
  have hset :
      d.support i.rev.succ ⋖
        d.support i.rev.castSucc := by
    rw [hins]
    exact Set.covBy_insert hxsmall
  refine ⟨?_, ?_⟩
  · simpa only [ascending, Fin.rev_castSucc,
      Fin.rev_succ, Subtype.mk_lt_mk] using hset.lt
  · intro Z hleft hright
    have hleft' :
        d.support i.rev.succ ⊂ (Z : Set E) := by
      have hleft0 :
          (d.ascending i.castSucc : Set E) <
            (Z : Set E) :=
        Subtype.coe_lt_coe.mpr hleft
      simpa only [coe_ascending, Fin.rev_castSucc,
        Fin.rev_succ] using hleft0
    have hright' :
        (Z : Set E) ⊂
          d.support i.rev.castSucc := by
      have hright0 :
          (Z : Set E) <
            (d.ascending i.succ : Set E) :=
        Subtype.coe_lt_coe.mpr hright
      simpa only [coe_ascending, Fin.rev_castSucc,
        Fin.rev_succ] using hright0
    exact hset.2
      hleft' hright'

/-- A saturated legal deletion chain determines a genuine maximal
closed-set flag. -/
def toClosedFlag
    (d : LegalDeletionChain c)
    (hempty : c.IsClosed ∅) :
    ClosedFlag c :=
  Flag.rangeFin d.ascending
    (d.ascending_zero hempty)
    d.ascending_last
    (fun i ↦ (d.ascending_covBy i).wcovBy)

@[simp]
theorem mem_toClosedFlag_iff
    (d : LegalDeletionChain c)
    (hempty : c.IsClosed ∅)
    (C : c.Closeds) :
    C ∈ d.toClosedFlag hempty ↔
      ∃ i, d.ascending i = C :=
  Iff.rfl

end LegalDeletionChain

namespace SaturatedOrderDeletionChain

universe v

variable {P : Type v} [PartialOrder P]
  {e : c.Closeds ≃o P}

/-- Pull a saturated target-poset chain back and read it bottom-to-top. -/
def ascending (d : SaturatedOrderDeletionChain e) :
    Fin (Fintype.card E + 1) → c.Closeds :=
  fun i ↦ e.symm (d.term i.rev)

theorem ascending_zero
    (d : SaturatedOrderDeletionChain e) :
    d.ascending 0 = ⊥ := by
  apply e.injective
  simp only [ascending, Fin.rev_zero,
    e.apply_symm_apply, d.bottom]

theorem ascending_last
    (d : SaturatedOrderDeletionChain e) :
    d.ascending (Fin.last (Fintype.card E)) = ⊤ := by
  apply e.injective
  simp only [ascending, Fin.rev_last,
    e.apply_symm_apply, d.top]

/-- Reversed consecutive target terms are covers in the source closed-set
poset. -/
theorem ascending_covBy
    (d : SaturatedOrderDeletionChain e)
    (i : Fin (Fintype.card E)) :
    d.ascending i.castSucc ⋖ d.ascending i.succ := by
  rw [ascending, ascending, apply_covBy_apply_iff]
  simpa only [Fin.rev_castSucc, Fin.rev_succ] using
    d.step_covBy i.rev

/-- Every saturated endpoint chain in an order-isomorphic target poset
determines a genuine maximal closed-set flag. -/
def toClosedFlag
    (d : SaturatedOrderDeletionChain e) :
    ClosedFlag c :=
  Flag.rangeFin d.ascending
    d.ascending_zero
    d.ascending_last
    (fun i ↦ (d.ascending_covBy i).wcovBy)

theorem mem_toClosedFlag_iff
    (d : SaturatedOrderDeletionChain e)
    (C : c.Closeds) :
    C ∈ d.toClosedFlag ↔
      ∃ i : Fin (Fintype.card E + 1),
        e.symm (d.term i.rev) = C :=
  Iff.rfl

/-- If a pulled-back saturated target chain has the same increasing
enumeration as a legal deletion chain, their maximal flags agree. -/
theorem toClosedFlag_eq_legalToClosedFlag
    (d : SaturatedOrderDeletionChain e)
    (l : LegalDeletionChain c)
    (hempty : c.IsClosed ∅)
    (h :
      ∀ i : Fin (Fintype.card E + 1),
        d.ascending i = l.ascending i) :
    d.toClosedFlag = l.toClosedFlag hempty := by
  apply Flag.ext
  ext C
  constructor
  · intro hC
    obtain ⟨i, hi⟩ :=
      (d.mem_toClosedFlag_iff C).1 hC
    apply
      (LegalDeletionChain.mem_toClosedFlag_iff
        l hempty C).2
    exact ⟨i, (h i) ▸ hi⟩
  · intro hC
    obtain ⟨i, hi⟩ :=
      (LegalDeletionChain.mem_toClosedFlag_iff
        l hempty C).1 hC
    apply (d.mem_toClosedFlag_iff C).2
    refine ⟨i, ?_⟩
    change d.ascending i = C
    rw [h i]
    exact hi

end SaturatedOrderDeletionChain

/-! ## Recovering the saturated presentation of a maximal flag -/

section FlagEnumeration

variable {α : Type*} [PartialOrder α] [BoundedOrder α]
  [Finite α]

omit [BoundedOrder α] [Finite α] in
/-- A cover between consecutive members of a maximal flag is already a
cover in the ambient poset.  This is the key non-tautological maximality
argument: an ambient point strictly between them would be comparable
with every flag member and could be inserted into the flag. -/
theorem Flag.ambient_covBy_of_covBy
    (s : Flag α) {a b : s} (hab : a ⋖ b) :
    a.1 ⋖ b.1 := by
  refine ⟨hab.lt, ?_⟩
  intro z haz hzb
  have hzmem : z ∈ s := by
    rw [Flag.mem_iff_forall_le_or_ge]
    intro x hx
    rcases s.le_or_le a.2 hx with hax | hxa
    · rcases s.le_or_le b.2 hx with hbx | hxb
      · exact Or.inl (hzb.le.trans hbx)
      ·
        let xs : s := ⟨x, hx⟩
        have haxs : a ≤ xs := hax
        have hxbs : xs ≤ b := hxb
        rcases hab.wcovBy.eq_or_eq haxs hxbs with hxa' | hxb'
        ·
          have hxa0 : x = a.1 :=
            congrArg Subtype.val hxa'
          exact Or.inr (by simpa [hxa0] using haz.le)
        ·
          have hxb0 : x = b.1 :=
            congrArg Subtype.val hxb'
          exact Or.inl (by simpa [hxb0] using hzb.le)
    · exact Or.inr (hxa.trans haz.le)
  let zs : s := ⟨z, hzmem⟩
  exact hab.2 (show a < zs from haz) (show zs < b from hzb)

/-- The increasing enumeration of a finite flag, with an explicit
cardinality equation to avoid casts in the domain. -/
def Flag.enumeration
    (s : Flag α) {n : ℕ}
    (hcard : Nat.card s = n + 1) :
    Fin (n + 1) ≃o s := by
  classical
  letI : Fintype s := Fintype.ofFinite s
  apply Fintype.orderIsoFinOfCardEq s
  simpa only [Nat.card_eq_fintype_card] using hcard

theorem Flag.enumeration_zero
    (s : Flag α) {n : ℕ}
    (hcard : Nat.card s = n + 1) :
    Flag.enumeration s hcard 0 = (⊥ : s) := by
  let e := Flag.enumeration s hcard
  apply le_antisymm
  · have h :
        (0 : Fin (n + 1)) ≤ e.symm (⊥ : s) :=
      Fin.zero_le _
    simpa only [e.apply_symm_apply] using e.monotone h
  · exact bot_le

theorem Flag.enumeration_last
    (s : Flag α) {n : ℕ}
    (hcard : Nat.card s = n + 1) :
    Flag.enumeration s hcard (Fin.last n) = (⊤ : s) := by
  let e := Flag.enumeration s hcard
  apply le_antisymm
  · exact le_top
  · have h :
        e.symm (⊤ : s) ≤ Fin.last n :=
      Fin.le_last _
    simpa only [e.apply_symm_apply] using e.monotone h

omit [BoundedOrder α] in
theorem Flag.enumeration_ambient_covBy
    (s : Flag α) {n : ℕ}
    (hcard : Nat.card s = n + 1)
    (i : Fin n) :
    (Flag.enumeration s hcard i.castSucc).1 ⋖
      (Flag.enumeration s hcard i.succ).1 := by
  apply Flag.ambient_covBy_of_covBy s
  rw [apply_covBy_apply_iff]
  rw [Fin.covBy_iff, Nat.covBy_iff_add_one_eq]
  rfl

end FlagEnumeration

/-! ## Exact rank and reconstruction for finite convex geometries -/

section ClosedFlagReconstruction

variable (hae : c.IsAntiExchange)
  (hempty : c.IsClosed ∅)

include hae hempty

/-- Along the increasing enumeration of a maximal closed-set flag,
the ground-set cardinality is exactly the index. -/
theorem ClosedFlag.enumeration_ncard
    (s : ClosedFlag c) {n : ℕ}
    (hcard : Nat.card s = n + 1) :
    ∀ i : Fin (n + 1),
      ((Flag.enumeration s hcard i).1 : Set E).ncard =
        i.1 := by
  intro i
  induction i using Fin.induction with
  | zero =>
      rw [Flag.enumeration_zero]
      change (c ∅).ncard = 0
      rw [hempty.closure_eq, Set.ncard_empty]
  | succ i ih =>
      have hcov :=
        Flag.enumeration_ambient_covBy s hcard i
      have hstep :=
        ncard_add_one_eq_of_covBy hae hcov
      calc
        ((Flag.enumeration s hcard i.succ).1 :
            Set E).ncard =
            ((Flag.enumeration s hcard i.castSucc).1 :
              Set E).ncard + 1 :=
          hstep.symm
        _ = i.1 + 1 := congrArg (· + 1) ih
        _ = i.succ.1 := rfl

/-- Every maximal flag of a finite convex geometry has exactly
`|E| + 1` terms. -/
theorem ClosedFlag.natCard_eq_groundCard_add_one
    (s : ClosedFlag c) :
    Nat.card s = Fintype.card E + 1 := by
  letI : Nonempty s :=
    ⟨⟨⊥, s.bot_mem⟩⟩
  obtain ⟨n, hcard⟩ :=
    Nat.exists_eq_succ_of_ne_zero
      (Nat.card_pos (α := s)).ne'
  have hrank :=
    ClosedFlag.enumeration_ncard hae hempty
      s hcard (Fin.last n)
  rw [Flag.enumeration_last] at hrank
  change ((⊤ : c.Closeds) : Set E).ncard = n at hrank
  have hn : n = Fintype.card E := by
    simpa only [coe_top, Set.ncard_univ,
      Nat.card_eq_fintype_card,
      Fin.val_last] using hrank.symm
  simpa only [hn] using hcard

/-- The rank-preserving increasing enumeration of a maximal
closed-set flag. -/
def ClosedFlag.groundEnumeration
    (s : ClosedFlag c) :
    Fin (Fintype.card E + 1) ≃o s :=
  Flag.enumeration s
    (ClosedFlag.natCard_eq_groundCard_add_one
      hae hempty s)

theorem ClosedFlag.groundEnumeration_zero
    (s : ClosedFlag c) :
    s.groundEnumeration hae hempty 0 = (⊥ : s) :=
  Flag.enumeration_zero s _

theorem ClosedFlag.groundEnumeration_last
    (s : ClosedFlag c) :
    s.groundEnumeration hae hempty
        (Fin.last (Fintype.card E)) =
      (⊤ : s) :=
  Flag.enumeration_last s _

theorem ClosedFlag.groundEnumeration_ambient_covBy
    (s : ClosedFlag c)
    (i : Fin (Fintype.card E)) :
    (s.groundEnumeration hae hempty i.castSucc).1 ⋖
      (s.groundEnumeration hae hempty i.succ).1 :=
  Flag.enumeration_ambient_covBy s _ i

/-- The unique point added at a step of the increasing flag
enumeration.  It is the point deleted at the reversed step. -/
def ClosedFlag.added
    (s : ClosedFlag c)
    (i : Fin (Fintype.card E)) : E :=
  Classical.choose
    (covBy_eq_insert hae
      (s.groundEnumeration_ambient_covBy
        hae hempty i))

theorem ClosedFlag.added_not_mem
    (s : ClosedFlag c)
    (i : Fin (Fintype.card E)) :
    s.added hae hempty i ∉
      ((s.groundEnumeration hae hempty
        i.castSucc).1 : Set E) :=
  (Classical.choose_spec
    (covBy_eq_insert hae
      (s.groundEnumeration_ambient_covBy
        hae hempty i))).1

theorem ClosedFlag.added_step
    (s : ClosedFlag c)
    (i : Fin (Fintype.card E)) :
    ((s.groundEnumeration hae hempty i.succ).1 :
        Set E) =
      insert (s.added hae hempty i)
        ((s.groundEnumeration hae hempty
          i.castSucc).1 : Set E) :=
  (Classical.choose_spec
    (covBy_eq_insert hae
      (s.groundEnumeration_ambient_covBy
        hae hempty i))).2

/-- Construct the top-to-bottom legal one-point deletion presentation
of a genuine maximal closed-set flag. -/
def ClosedFlag.toLegalDeletionChain
    (s : ClosedFlag c) :
    LegalDeletionChain c where
  support i :=
    ((s.groundEnumeration hae hempty i.rev).1 : Set E)
  closed i :=
    (s.groundEnumeration hae hempty i.rev).1.2
  removed i :=
    s.added hae hempty i.rev
  top := by
    have h :=
      congrArg
        (fun C : s ↦ (C.1 : Set E))
        (s.groundEnumeration_last hae hempty)
    change
      ((s.groundEnumeration hae hempty
        (Fin.last (Fintype.card E))).1 : Set E) =
          ((⊤ : c.Closeds) : Set E) at h
    simpa only [Fin.rev_zero, coe_top] using h
  bottom := by
    have h :=
      congrArg
        (fun C : s ↦ (C.1 : Set E))
        (s.groundEnumeration_zero hae hempty)
    change
      ((s.groundEnumeration hae hempty 0).1 : Set E) =
        ((⊥ : c.Closeds) : Set E) at h
    simpa only [Fin.rev_last, coe_bot,
      hempty.closure_eq] using h
  removed_mem i := by
    rw [Fin.rev_castSucc]
    rw [s.added_step hae hempty i.rev]
    exact Set.mem_insert _ _
  step i := by
    rw [Fin.rev_succ, Fin.rev_castSucc]
    rw [s.added_step hae hempty i.rev]
    exact
      (Set.insert_sdiff_self_of_notMem
        (s.added_not_mem hae hempty i.rev)).symm

@[simp]
theorem ClosedFlag.toLegalDeletionChain_ascending
    (s : ClosedFlag c)
    (i : Fin (Fintype.card E + 1)) :
    (s.toLegalDeletionChain hae hempty).ascending i =
      (s.groundEnumeration hae hempty i).1 := by
  apply Subtype.ext
  simp only [LegalDeletionChain.coe_ascending,
    ClosedFlag.toLegalDeletionChain, Fin.rev_rev]

/-- Reconstructing the maximal flag from its legal deletion
presentation recovers the original flag. -/
theorem ClosedFlag.toClosedFlag_toLegalDeletionChain
    (s : ClosedFlag c) :
    (s.toLegalDeletionChain hae hempty).toClosedFlag
        hempty =
      s := by
  apply Flag.ext
  ext C
  constructor
  · intro hC
    obtain ⟨i, hi⟩ :=
      (LegalDeletionChain.mem_toClosedFlag_iff
        (s.toLegalDeletionChain hae hempty)
        hempty C).1 hC
    rw [s.toLegalDeletionChain_ascending hae hempty] at hi
    rw [← hi]
    exact
      (s.groundEnumeration hae hempty i).2
  · intro hC
    obtain ⟨i, hi⟩ :=
      (s.groundEnumeration hae hempty).surjective
        ⟨C, hC⟩
    apply
      (LegalDeletionChain.mem_toClosedFlag_iff
        (s.toLegalDeletionChain hae hempty)
        hempty C).2
    refine ⟨i, ?_⟩
    rw [s.toLegalDeletionChain_ascending hae hempty]
    exact congrArg Subtype.val hi

end ClosedFlagReconstruction

end QuotientSubmoduleEquidistribution.SetClosure
