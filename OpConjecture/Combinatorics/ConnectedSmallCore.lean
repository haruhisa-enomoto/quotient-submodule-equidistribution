import OpConjecture.Combinatorics.BottomThreeFourFaithfulRecurrence

/-!
# Connected small faithful cores

This file formalizes the exact *use interface* of the connected small-core
argument in the repaired bottom-three/bottom-four proof.  It does not assert
the representation-theoretic classification.  Instead it proves all finite
cardinality bookkeeping after the following source-faithful inputs are
supplied:

* `0 < v <= d`, where `v` is the number of simple modules and `d` is the
  common faithful-core size;
* `v = d` implies hereditary Dynkin;
* `v = 1` implies Nakayama;
* `v = 2, d = 3` implies Nakayama or one of the two square-zero lollipops,
  in either orientation;
* hereditary Dynkin and Nakayama algebras have equal full level
  polynomials; and
* each lollipop has exactly two closed one-point extensions of each
  three-object faithful core.

The last item is represented by an equivalence with `Fin 2`, not by a bare
numerical assumption.  The generic one-point-extension theorem below proves
that this table gives faithful degree-four count `2`.
-/

noncomputable section

open Set

namespace OpConjecture.BottomLevels.ConnectedSmallCore

universe u v w

/-! ## The four lollipop possibilities -/

/-- The two relation variants for the quiver with one loop `x` and one
cross-arrow `a`:

* `deadPath` is `kQ/(x^2, x a)`;
* `livePath` is `kQ/(x^2)`.
-/
inductive LollipopRelation where
  | deadPath
  | livePath
  deriving DecidableEq, Fintype

/-- The source orientation and its opposite. -/
inductive LollipopOrientation where
  | forward
  | opposite
  deriving DecidableEq, Fintype

/-- Exactly the two relation variants and their opposites. -/
structure LollipopKind where
  relation : LollipopRelation
  orientation : LollipopOrientation
  deriving DecidableEq, Fintype

/-! ## Pure arithmetic form of the connected classification -/

/--
The exact classification interface used by the repaired proof.

`coreSize` is the common cardinality `d` of the two minimal faithful cores,
and `simpleCount` is the number `v` of simples (equivalently, in the basic
scope, indecomposable projectives).  The final field is deliberately only
the residual pair `v = 2, d = 3`; all other small cases are derived below by
arithmetic.
-/
structure ClassificationData
    {B : Type u}
    (coreSize simpleCount : B → ℕ)
    (Connected HereditaryDynkin Nakayama : B → Prop)
    (IsLollipop : B → LollipopKind → Prop) : Prop where
  simpleCount_pos :
    ∀ b, Connected b → 0 < simpleCount b
  simpleCount_le_coreSize :
    ∀ b, Connected b → simpleCount b ≤ coreSize b
  hereditaryDynkin_of_eq :
    ∀ b, Connected b → simpleCount b = coreSize b →
      HereditaryDynkin b
  nakayama_of_simpleCount_eq_one :
    ∀ b, Connected b → simpleCount b = 1 → Nakayama b
  twoSimple_coreThree :
    ∀ b, Connected b → simpleCount b = 2 → coreSize b = 3 →
      Nakayama b ∨ ∃ kind, IsLollipop b kind

namespace ClassificationData

variable {B : Type u}
  {coreSize simpleCount : B → ℕ}
  {Connected HereditaryDynkin Nakayama : B → Prop}
  {IsLollipop : B → LollipopKind → Prop}

/-- If the connected faithful core has size below three, only the
hereditary-Dynkin and Nakayama branches can occur. -/
theorem classify_of_coreSize_lt_three
    (D : ClassificationData coreSize simpleCount Connected
      HereditaryDynkin Nakayama IsLollipop)
    {b : B} (hb : Connected b) (hd : coreSize b < 3) :
    HereditaryDynkin b ∨ Nakayama b := by
  by_cases heq : simpleCount b = coreSize b
  · exact Or.inl (D.hereditaryDynkin_of_eq b hb heq)
  · right
    apply D.nakayama_of_simpleCount_eq_one b hb
    have hpos := D.simpleCount_pos b hb
    have hle := D.simpleCount_le_coreSize b hb
    omega

/-- If the connected faithful core has size below four, the only branch in
addition to hereditary Dynkin and Nakayama is the two-simple, core-size-three
lollipop branch. -/
theorem classify_of_coreSize_lt_four
    (D : ClassificationData coreSize simpleCount Connected
      HereditaryDynkin Nakayama IsLollipop)
    {b : B} (hb : Connected b) (hd : coreSize b < 4) :
    HereditaryDynkin b ∨ Nakayama b ∨
      ∃ kind, IsLollipop b kind := by
  by_cases heq : simpleCount b = coreSize b
  · exact Or.inl (D.hereditaryDynkin_of_eq b hb heq)
  · have hpos := D.simpleCount_pos b hb
    have hle := D.simpleCount_le_coreSize b hb
    by_cases hone : simpleCount b = 1
    · exact Or.inr (Or.inl
        (D.nakayama_of_simpleCount_eq_one b hb hone))
    · have hv : simpleCount b = 2 := by omega
      have hd3 : coreSize b = 3 := by omega
      rcases D.twoSimple_coreThree b hb hv hd3 with hN | hL
      · exact Or.inr (Or.inl hN)
      · exact Or.inr (Or.inr hL)

end ClassificationData

/-! ## Faithful core plus one point -/

namespace OnePointTable

variable {E : Type v} [Finite E]
  {c : OpConjecture.SetClosure E}
  {Faithful : Set E → Prop}

/-- Labels outside the minimal faithful core whose one-point extension is
already closed.  These are exactly the faithful closed sets one level above
the core. -/
def ClosedExtension
    (D : MinimalFaithfulCore.Data c Faithful) : Type v :=
  {x : E //
    x ∉ (D.core : Set E) ∧
      c.IsClosed (insert x (D.core : Set E))}

/-- Send a good outside label to the corresponding faithful closed
one-point extension of the core. -/
def toFaithfulLevel
    (D : MinimalFaithfulCore.Data c Faithful)
    (hFaithful : Monotone Faithful) :
    ClosedExtension D →
      {C : c.Closeds //
        Faithful (C : Set E) ∧
          (C : Set E).ncard = (D.core : Set E).ncard + 1} :=
  fun x ↦
    ⟨⟨insert x.1 (D.core : Set E), x.2.2⟩,
      ⟨hFaithful (subset_insert x.1 (D.core : Set E)) D.core_faithful,
        Set.ncard_insert_of_notMem x.2.1⟩⟩

/-- The good-outside-label parametrization is injective. -/
theorem toFaithfulLevel_injective
    (D : MinimalFaithfulCore.Data c Faithful)
    (hFaithful : Monotone Faithful) :
    Function.Injective (toFaithfulLevel D hFaithful) := by
  intro x y hxy
  have hsets :
      insert x.1 (D.core : Set E) =
        insert y.1 (D.core : Set E) := by
    exact congrArg (fun C ↦ (C.1 : Set E)) hxy
  apply Subtype.ext
  have hxmem : x.1 ∈ insert y.1 (D.core : Set E) := by
    rw [← hsets]
    exact Set.mem_insert x.1 (D.core : Set E)
  rcases hxmem with hxy' | hxcore
  · exact hxy'
  · exact (x.2.1 hxcore).elim

/-- Every faithful closed set one level above the core is obtained by
adjoining a unique good outside label. -/
theorem toFaithfulLevel_surjective
    (D : MinimalFaithfulCore.Data c Faithful)
    (hFaithful : Monotone Faithful) :
    Function.Surjective (toFaithfulLevel D hFaithful) := by
  intro C
  have hsubset :
      (D.core : Set E) ⊆ (C.1 : Set E) :=
    D.core_le C.1 C.2.1
  have hcard :
      (D.core : Set E).ncard + 1 = (C.1 : Set E).ncard :=
    C.2.2.symm
  obtain ⟨x, hxcore, hx⟩ :=
    (Set.exists_eq_insert_iff_ncard
      (s := (D.core : Set E)) (t := (C.1 : Set E))).2
      ⟨hsubset, hcard⟩
  let x' : ClosedExtension D :=
    ⟨x, hxcore, by simpa [hx] using C.1.property⟩
  refine ⟨x', ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hx

/-- Exact equivalence between good outside labels and faithful closed sets
one cardinality level above the core. -/
def faithfulLevelEquivClosedExtension
    (D : MinimalFaithfulCore.Data c Faithful)
    (hFaithful : Monotone Faithful) :
    {C : c.Closeds //
        Faithful (C : Set E) ∧
          (C : Set E).ncard = (D.core : Set E).ncard + 1} ≃
      ClosedExtension D :=
  (Equiv.ofBijective (toFaithfulLevel D hFaithful)
    ⟨toFaithfulLevel_injective D hFaithful,
      toFaithfulLevel_surjective D hFaithful⟩).symm

/-- The faithful coefficient immediately above the core is the number of
closed one-point core extensions. -/
theorem faithfulLevelCount_succ_core
    (D : MinimalFaithfulCore.Data c Faithful)
    (hFaithful : Monotone Faithful) :
    MinimalFaithfulCore.faithfulLevelCount c Faithful
        ((D.core : Set E).ncard + 1) =
      Nat.card (ClosedExtension D) := by
  unfold MinimalFaithfulCore.faithfulLevelCount
  calc
    (MinimalFaithfulCore.faithfulLevel c Faithful
          ((D.core : Set E).ncard + 1)).ncard =
        Nat.card
          {C : c.Closeds //
            C ∈ MinimalFaithfulCore.faithfulLevel c Faithful
              ((D.core : Set E).ncard + 1)} :=
      (Nat.card_coe_set_eq _).symm
    _ = Nat.card (ClosedExtension D) :=
      Nat.card_congr (faithfulLevelEquivClosedExtension D hFaithful)

/-- A three-object faithful core with exactly two good one-point extensions
has faithful degree-four count two. -/
theorem faithfulLevelCount_four_eq_two
    (D : MinimalFaithfulCore.Data c Faithful)
    (hFaithful : Monotone Faithful)
    (hcore : (D.core : Set E).ncard = 3)
    (htable : ClosedExtension D ≃ Fin 2) :
    MinimalFaithfulCore.faithfulLevelCount c Faithful 4 = 2 := by
  have hcount := faithfulLevelCount_succ_core D hFaithful
  rw [hcore] at hcount
  norm_num at hcount ⊢
  calc
    MinimalFaithfulCore.faithfulLevelCount c Faithful 4 =
        Nat.card (ClosedExtension D) := hcount
    _ = Nat.card (Fin 2) := Nat.card_congr htable
    _ = 2 := by simp

/-- The exact finite table datum required from one lollipop side. -/
structure TwoExtensionData
    (D : MinimalFaithfulCore.Data c Faithful) where
  faithful_monotone : Monotone Faithful
  core_ncard : (D.core : Set E).ncard = 3
  closedExtensions : ClosedExtension D ≃ Fin 2

/-- A source-facing form of the table: two named good outsiders, proved
distinct, and an exhaustion assertion saying that every good outsider is one
of them.  This is the minimal content of the displayed `L₀`/`L₁` Hom
tables needed by the coefficient proof. -/
structure NamedTwoExtensionData
    (D : MinimalFaithfulCore.Data c Faithful) where
  faithful_monotone : Monotone Faithful
  core_ncard : (D.core : Set E).ncard = 3
  good₀ : E
  good₁ : E
  good_ne : good₀ ≠ good₁
  good₀_not_core : good₀ ∉ (D.core : Set E)
  good₁_not_core : good₁ ∉ (D.core : Set E)
  good₀_closed : c.IsClosed (insert good₀ (D.core : Set E))
  good₁_closed : c.IsClosed (insert good₁ (D.core : Set E))
  exhaustive :
    ∀ z : E, z ∉ (D.core : Set E) →
      c.IsClosed (insert z (D.core : Set E)) →
      z = good₀ ∨ z = good₁

namespace NamedTwoExtensionData

variable {D : MinimalFaithfulCore.Data c Faithful}

/-- Enumerate the two named good extensions by `Bool`. -/
def boolToClosedExtension
    (T : NamedTwoExtensionData D) : Bool → ClosedExtension D
  | false => ⟨T.good₀, T.good₀_not_core, T.good₀_closed⟩
  | true => ⟨T.good₁, T.good₁_not_core, T.good₁_closed⟩

omit [Finite E] in
theorem boolToClosedExtension_injective
    (T : NamedTwoExtensionData D) :
    Function.Injective T.boolToClosedExtension := by
  intro x y hxy
  cases x <;> cases y
  · rfl
  · exact (T.good_ne (congrArg Subtype.val hxy)).elim
  · exact (T.good_ne (congrArg Subtype.val hxy).symm).elim
  · rfl

omit [Finite E] in
theorem boolToClosedExtension_surjective
    (T : NamedTwoExtensionData D) :
    Function.Surjective T.boolToClosedExtension := by
  intro z
  rcases T.exhaustive z.1 z.2.1 z.2.2 with hz | hz
  · refine ⟨false, ?_⟩
    apply Subtype.ext
    exact hz.symm
  · refine ⟨true, ?_⟩
    apply Subtype.ext
    exact hz.symm

/-- Convert the two named rows into the exact `Fin 2` table datum. -/
def closedExtensionsEquivFinTwo
    (T : NamedTwoExtensionData D) : ClosedExtension D ≃ Fin 2 :=
  (Equiv.ofBijective T.boolToClosedExtension
    ⟨T.boolToClosedExtension_injective,
      T.boolToClosedExtension_surjective⟩).symm.trans
    finTwoEquiv.symm

/-- Forget the names after their table has been verified. -/
def toTwoExtensionData
    (T : NamedTwoExtensionData D) : TwoExtensionData D where
  faithful_monotone := T.faithful_monotone
  core_ncard := T.core_ncard
  closedExtensions := T.closedExtensionsEquivFinTwo

end NamedTwoExtensionData

/-- A two-extension table proves faithful degree-four count two. -/
theorem TwoExtensionData.faithfulLevelCount_four_eq_two
    {D : MinimalFaithfulCore.Data c Faithful}
    (T : TwoExtensionData D) :
    MinimalFaithfulCore.faithfulLevelCount c Faithful 4 = 2 :=
  OnePointTable.faithfulLevelCount_four_eq_two D T.faithful_monotone
    T.core_ncard T.closedExtensions

/-- Named-table specialization. -/
theorem NamedTwoExtensionData.faithfulLevelCount_four_eq_two
    {D : MinimalFaithfulCore.Data c Faithful}
    (T : NamedTwoExtensionData D) :
    MinimalFaithfulCore.faithfulLevelCount c Faithful 4 = 2 :=
  T.toTwoExtensionData.faithfulLevelCount_four_eq_two

end OnePointTable

/-! ## Adapter to the repaired recurrence -/

variable {B : Type u}
  (Index : B → Type v)
  [∀ b : B, Finite (Index b)]
  (cQ cS : ∀ b : B, OpConjecture.SetClosure (Index b))
  (FaithfulQ FaithfulS : ∀ b : B, Set (Index b) → Prop)
  (QCore : ∀ b : B,
    MinimalFaithfulCore.Data (cQ b) (FaithfulQ b))
  (SCore : ∀ b : B,
    MinimalFaithfulCore.Data (cS b) (FaithfulS b))

/-- The quotient-side faithful core size used by the classification.  Ringel
supplies equality with the submodule-side core size elsewhere. -/
abbrev coreSize (b : B) : ℕ :=
  ((QCore b).core : Set (Index b)).ncard

/-- A full-profile theorem in either class gives every level equality
needed by the small-core recurrence. -/
abbrev FullProfileEquality (b : B) : Prop :=
  (cQ b).levelPolynomial = (cS b).levelPolynomial

/-- The exact pair of one-point closure tables required for one classified
lollipop algebra. -/
structure LollipopTableData (b : B) where
  quotient : OnePointTable.TwoExtensionData (QCore b)
  submodule : OnePointTable.TwoExtensionData (SCore b)

/--
The exact `ThreeFourCoreRecurrenceData.smallCore` field follows from the
connected classification, full Dynkin/Nakayama profile endpoints, and the
lollipop faithful table.

At level three the lollipop branch is arithmetically impossible because its
core already has size three.  At level four the table is used directly.
-/
theorem smallCore_of_classification
    (simpleCount : B → ℕ)
    (Connected HereditaryDynkin Nakayama : B → Prop)
    (IsLollipop : B → LollipopKind → Prop)
    (D : ClassificationData (coreSize Index cQ FaithfulQ QCore) simpleCount Connected
      HereditaryDynkin Nakayama IsLollipop)
    (hDynkin :
      ∀ b, HereditaryDynkin b →
        FullProfileEquality Index cQ cS b)
    (hNakayama :
      ∀ b, Nakayama b →
        FullProfileEquality Index cQ cS b)
    (hLollipop :
      ∀ b kind, IsLollipop b kind →
        BottomThreeFourFaithfulRecurrence.faithfulQCount
            Index cQ FaithfulQ b 4 =
          BottomThreeFourFaithfulRecurrence.faithfulSCount
            Index cS FaithfulS b 4) :
    ∀ (b : B) (n : ℕ), n = 3 ∨ n = 4 → Connected b →
      ((QCore b).core : Set (Index b)).ncard < n →
      (BottomThreeFourFaithfulRecurrence.faithfulQCount
            Index cQ FaithfulQ b n =
          BottomThreeFourFaithfulRecurrence.faithfulSCount
            Index cS FaithfulS b n) ∨
        (cQ b).levelCount n = (cS b).levelCount n := by
  intro b n hn hb hsmall
  rcases hn with rfl | rfl
  · rcases D.classify_of_coreSize_lt_three hb hsmall with hD | hN
    · exact Or.inr
        ((OpConjecture.SetClosure.levelPolynomial_eq_iff
          (cQ b) (cS b)).1 (hDynkin b hD) 3)
    · exact Or.inr
        ((OpConjecture.SetClosure.levelPolynomial_eq_iff
          (cQ b) (cS b)).1 (hNakayama b hN) 3)
  · rcases D.classify_of_coreSize_lt_four hb hsmall with hD | hN | ⟨kind, hL⟩
    · exact Or.inr
        ((OpConjecture.SetClosure.levelPolynomial_eq_iff
          (cQ b) (cS b)).1 (hDynkin b hD) 4)
    · exact Or.inr
        ((OpConjecture.SetClosure.levelPolynomial_eq_iff
          (cQ b) (cS b)).1 (hNakayama b hN) 4)
    · exact Or.inl (hLollipop b kind hL)

/-- Package two exact one-point tables into the faithful lollipop equality
expected by `smallCore_of_classification`. -/
theorem lollipop_faithful_four_eq_of_twoExtensionTables
    {b : B}
    (TQ : OnePointTable.TwoExtensionData (QCore b))
    (TS : OnePointTable.TwoExtensionData (SCore b)) :
    BottomThreeFourFaithfulRecurrence.faithfulQCount
        Index cQ FaithfulQ b 4 =
      BottomThreeFourFaithfulRecurrence.faithfulSCount
        Index cS FaithfulS b 4 := by
  change
    MinimalFaithfulCore.faithfulLevelCount (cQ b) (FaithfulQ b) 4 =
      MinimalFaithfulCore.faithfulLevelCount (cS b) (FaithfulS b) 4
  rw [TQ.faithfulLevelCount_four_eq_two,
    TS.faithfulLevelCount_four_eq_two]

/-- A packaged lollipop table has equal faithful degree-four counts. -/
theorem LollipopTableData.faithful_four_eq
    {b : B}
    (T : LollipopTableData Index cQ cS FaithfulQ FaithfulS QCore SCore b) :
    BottomThreeFourFaithfulRecurrence.faithfulQCount
        Index cQ FaithfulQ b 4 =
      BottomThreeFourFaithfulRecurrence.faithfulSCount
        Index cS FaithfulS b 4 :=
  lollipop_faithful_four_eq_of_twoExtensionTables
    Index cQ cS FaithfulQ FaithfulS QCore SCore
    T.quotient T.submodule

/-- One-call form of the connected adapter.  Its remaining lollipop input is
literally a pair of exact two-extension tables for each classified relation
variant and orientation. -/
theorem smallCore_of_classification_and_lollipopTables
    (simpleCount : B → ℕ)
    (Connected HereditaryDynkin Nakayama : B → Prop)
    (IsLollipop : B → LollipopKind → Prop)
    (D : ClassificationData (coreSize Index cQ FaithfulQ QCore) simpleCount Connected
      HereditaryDynkin Nakayama IsLollipop)
    (hDynkin :
      ∀ b, HereditaryDynkin b →
        FullProfileEquality Index cQ cS b)
    (hNakayama :
      ∀ b, Nakayama b →
        FullProfileEquality Index cQ cS b)
    (hTables :
      ∀ b kind, IsLollipop b kind →
        LollipopTableData Index cQ cS FaithfulQ FaithfulS QCore SCore b) :
    ∀ (b : B) (n : ℕ), n = 3 ∨ n = 4 → Connected b →
      ((QCore b).core : Set (Index b)).ncard < n →
      (BottomThreeFourFaithfulRecurrence.faithfulQCount
            Index cQ FaithfulQ b n =
          BottomThreeFourFaithfulRecurrence.faithfulSCount
            Index cS FaithfulS b n) ∨
        (cQ b).levelCount n = (cS b).levelCount n := by
  apply smallCore_of_classification
    Index cQ cS FaithfulQ FaithfulS QCore
    simpleCount Connected HereditaryDynkin Nakayama IsLollipop
    D hDynkin hNakayama
  intro b kind hL
  exact (hTables b kind hL).faithful_four_eq

end OpConjecture.BottomLevels.ConnectedSmallCore
