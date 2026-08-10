import OpConjecture.RepresentationTheory.LengthThreeUniserial

/-!
# Quotient-side exhaustiveness at closure level three

This file develops the quotient-side exhaustiveness argument for
`paper/op_conjecture/level-four.tex`.  The first part proves the unconditional
coarse partition of a quotient-closed three-element support by the number of
nonsimple members.  The second part defines literal data for the five
manuscript families and isolates the two remaining local representation-
theoretic refinements.
-/

noncomputable section

open Set
open CategoryTheory CategoryTheory.Limits

namespace OpConjecture.IndecomposableSkeleton

universe u v w

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-! ## The unconditional coarse partition -/

/-- A quotient-closed support with exactly three skeleton indices. -/
structure QClosedTriple where
  support : Set ι
  closed : σ.qClosure.IsClosed support
  ncard_support : support.ncard = 3

/-- The three coarse possibilities, before identifying the two branching
patterns representation-theoretically. -/
inductive QClosedTripleCoarseShape (S : Set ι) : Prop
  | allSimple
      (simple : ∀ i ∈ S, Simple (σ.obj i))
  | oneNonsimple
      (x s t : ι)
      (x_ne_s : x ≠ s) (x_ne_t : x ≠ t) (s_ne_t : s ≠ t)
      (support_eq : S = {x, s, t})
      (x_nonsimple : ¬ Simple (σ.obj x))
      (s_simple : Simple (σ.obj s))
      (t_simple : Simple (σ.obj t))
  | twoNonsimple
      (x y s : ι)
      (x_ne_y : x ≠ y) (x_ne_s : x ≠ s) (y_ne_s : y ≠ s)
      (support_eq : S = {x, y, s})
      (x_nonsimple : ¬ Simple (σ.obj x))
      (y_nonsimple : ¬ Simple (σ.obj y))
      (s_simple : Simple (σ.obj s))

/-- Every nonempty quotient-closed support contains a simple member. -/
theorem exists_simple_mem_of_qClosure_isClosed_of_nonempty
    {S : Set ι} (hclosed : σ.qClosure.IsClosed S)
    (hne : S.Nonempty) :
    ∃ s ∈ S, Simple (σ.obj s) := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨Q⟩ := σ.exists_simpleQuotient x
  exact ⟨Q.index, Q.mem_of_isClosed σ hclosed hx, Q.simple⟩

/-- Unconditionally, a quotient-closed three-support has either zero, one,
or two nonsimple members, and the three cases have the displayed literal
supports.  The impossible fourth possibility (three nonsimple members) is
excluded by taking a simple quotient of any selected member. -/
theorem qClosedTriple_coarse_exhaustive
    {S : Set ι} (hcard : S.ncard = 3)
    (hclosed : σ.qClosure.IsClosed S) :
    QClosedTripleCoarseShape σ S := by
  classical
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Set.ncard_eq_three.mp hcard
  by_cases ha : Simple (σ.obj a)
  · by_cases hb : Simple (σ.obj b)
    · by_cases hc : Simple (σ.obj c)
      · exact .allSimple (by
          intro i hi
          rcases (by simpa using hi) with rfl | rfl | rfl
          · exact ha
          · exact hb
          · exact hc)
      · exact .oneNonsimple c a b hac.symm hbc.symm hab
          (by ext i; simp [or_comm, or_left_comm]) hc ha hb
    · by_cases hc : Simple (σ.obj c)
      · exact .oneNonsimple b a c hab.symm hbc hac
          (by ext i; simp [or_left_comm]) hb ha hc
      · exact .twoNonsimple b c a hbc hab.symm hac.symm
          (by ext i; simp [or_comm, or_left_comm]) hb hc ha
  · by_cases hb : Simple (σ.obj b)
    · by_cases hc : Simple (σ.obj c)
      · exact .oneNonsimple a b c hab hac hbc
          rfl ha hb hc
      · exact .twoNonsimple a c b hac hab hbc.symm
          (by ext i; simp [or_comm]) ha hc hb
    · by_cases hc : Simple (σ.obj c)
      · exact .twoNonsimple a b c hab hac hbc rfl ha hb hc
      · exfalso
        have hnonempty : ({a, b, c} : Set ι).Nonempty := ⟨a, by simp⟩
        obtain ⟨s, hs, hsimple⟩ :=
          σ.exists_simple_mem_of_qClosure_isClosed_of_nonempty
            hclosed hnonempty
        rcases (by simpa using hs) with rfl | rfl | rfl
        · exact ha hsimple
        · exact hb hsimple
        · exact hc hsimple

/-! ## Literal five-family data -/

/-- Family 1: three pairwise distinct simple representatives. -/
structure QTripleFamilyOneData where
  a : ι
  b : ι
  c : ι
  a_ne_b : a ≠ b
  a_ne_c : a ≠ c
  b_ne_c : b ≠ c
  a_simple : Simple (σ.obj a)
  b_simple : Simple (σ.obj b)
  c_simple : Simple (σ.obj c)

/-- Family 2: a length-two representative, its simple top, and one further
simple representative. -/
structure QTripleFamilyTwoData where
  x : σ.LengthTwoIndex
  top : σ.SimpleQuotient x.1
  extra : σ.SimpleIndex
  extra_ne_top : extra.1 ≠ top.index

/-- Family 3: two different length-two representatives with the same simple
top, together with that top. -/
structure QTripleFamilyThreeData where
  x : σ.LengthTwoIndex
  y : σ.LengthTwoIndex
  x_ne_y : x ≠ y
  x_top : σ.SimpleQuotient x.1
  y_top : σ.SimpleQuotient y.1
  same_top : x_top.index = y_top.index

/-- Family 4: a length-three uniserial representative and its two proper
nonzero quotient types. -/
structure QTripleFamilyFourData where
  x : σ.LengthThreeUniserialIndex
  chain : σ.LengthThreeQuotientChain x

/-- Family 5 in an intrinsic form: a length-three representative with simple
radical and two different simple quotient types.  Its top has length two and
contains both displayed simple types; this is the manuscript's branched
Loewy-length-two family. -/
structure QTripleFamilyFiveData where
  x : ι
  length_three : σ.compositionLength x = 3
  radical_simple : IsSimpleModule R (σ.moduleRadical x)
  left : σ.SimpleQuotient x
  right : σ.SimpleQuotient x
  quotient_types_ne : left.index ≠ right.index

def QTripleFamilyOneData.support (D : σ.QTripleFamilyOneData) : Set ι :=
  {D.a, D.b, D.c}

def QTripleFamilyTwoData.support (D : σ.QTripleFamilyTwoData) : Set ι :=
  {D.x.1, D.top.index, D.extra.1}

def QTripleFamilyThreeData.support (D : σ.QTripleFamilyThreeData) : Set ι :=
  {D.x.1, D.y.1, D.x_top.index}

def QTripleFamilyFourData.support (D : σ.QTripleFamilyFourData) : Set ι :=
  D.chain.support

def QTripleFamilyFiveData.support (D : σ.QTripleFamilyFiveData) : Set ι :=
  {D.x, D.left.index, D.right.index}

/-- Family predicates are mere inhabitance of the corresponding witness
data. -/
abbrev QTripleFamilyOne (S : Set ι) : Prop :=
  ∃ D : σ.QTripleFamilyOneData, S = D.support

abbrev QTripleFamilyTwo (S : Set ι) : Prop :=
  ∃ D : σ.QTripleFamilyTwoData, S = D.support

abbrev QTripleFamilyThree (S : Set ι) : Prop :=
  ∃ D : σ.QTripleFamilyThreeData, S = D.support

abbrev QTripleFamilyFour (S : Set ι) : Prop :=
  ∃ D : σ.QTripleFamilyFourData, S = D.support

abbrev QTripleFamilyFive (S : Set ι) : Prop :=
  ∃ D : σ.QTripleFamilyFiveData, S = D.support

/-- The tagged disjunction of the five literal quotient-side families. -/
inductive QTripleFamily (S : Set ι) : Prop
  | one (h : σ.QTripleFamilyOne S)
  | two (h : σ.QTripleFamilyTwo S)
  | three (h : σ.QTripleFamilyThree S)
  | four (h : σ.QTripleFamilyFour S)
  | five (h : σ.QTripleFamilyFive S)

/-- The nonsimple part of a support. -/
def nonsimplePart (S : Set ι) : Set ι :=
  {i | i ∈ S ∧ ¬ Simple (σ.obj i)}

theorem not_simple_of_compositionLength_eq_three
    {i : ι} (hi : σ.compositionLength i = 3) :
    ¬ Simple (σ.obj i) := by
  intro hsimple
  have hone := (σ.compositionLength_eq_one_iff_simple i).2 hsimple
  omega

/-- Family 1 has no nonsimple member. -/
theorem nonsimplePart_eq_empty_of_familyOne
    {S : Set ι} (h : σ.QTripleFamilyOne S) :
    σ.nonsimplePart S = ∅ := by
  obtain ⟨D, hS⟩ := h
  ext i
  simp only [nonsimplePart, mem_setOf_eq, mem_empty_iff_false, iff_false]
  rintro ⟨hi, hinsimple⟩
  rw [hS, QTripleFamilyOneData.support] at hi
  rcases (by simpa using hi) with rfl | rfl | rfl
  · exact hinsimple D.a_simple
  · exact hinsimple D.b_simple
  · exact hinsimple D.c_simple

/-- Family 2 has exactly its length-two member as nonsimple part. -/
theorem nonsimplePart_eq_singleton_of_familyTwo
    {S : Set ι} (h : σ.QTripleFamilyTwo S) :
    ∃ x : ι, σ.nonsimplePart S = {x} := by
  classical
  obtain ⟨D, hS⟩ := h
  refine ⟨D.x.1, ?_⟩
  have hxn : ¬ Simple (σ.obj D.x.1) :=
    σ.lengthTwoIndex_not_simple D.x
  ext i
  constructor
  · rintro ⟨hi, hinsimple⟩
    have hiD : i ∈ D.support := by
      rw [← hS]
      exact hi
    have hi' : i ∈ ({D.x.1, D.top.index, D.extra.1} : Set ι) :=
      by simpa [QTripleFamilyTwoData.support] using hiD
    rcases (by simpa using hi') with hix | hitop | hiextra
    · simp [hix]
    · exact False.elim (hinsimple (by simpa [hitop] using D.top.simple))
    · exact False.elim (hinsimple (by simpa [hiextra] using D.extra.2))
  · intro hi
    have hix : i = D.x.1 := by simpa using hi
    subst i
    exact ⟨by rw [hS, QTripleFamilyTwoData.support]; simp, hxn⟩

/-- Family 3 has exactly its two length-two members as nonsimple part. -/
theorem nonsimplePart_eq_pair_of_familyThree
    {S : Set ι} (h : σ.QTripleFamilyThree S) :
    ∃ x y : ι, x ≠ y ∧ σ.nonsimplePart S = {x, y} := by
  classical
  obtain ⟨D, hS⟩ := h
  have hxy : D.x.1 ≠ D.y.1 := by
    intro heq
    exact D.x_ne_y (Subtype.ext heq)
  refine ⟨D.x.1, D.y.1, hxy, ?_⟩
  have hxn : ¬ Simple (σ.obj D.x.1) :=
    σ.lengthTwoIndex_not_simple D.x
  have hyn : ¬ Simple (σ.obj D.y.1) :=
    σ.lengthTwoIndex_not_simple D.y
  ext i
  constructor
  · rintro ⟨hi, hinsimple⟩
    have hiD : i ∈ D.support := by
      rw [← hS]
      exact hi
    have hi' : i ∈ ({D.x.1, D.y.1, D.x_top.index} : Set ι) :=
      by simpa [QTripleFamilyThreeData.support] using hiD
    rcases (by simpa using hi') with hix | hiy | hitop
    · simp [hix]
    · simp [hiy]
    · exact False.elim (hinsimple (by simpa [hitop] using D.x_top.simple))
  · intro hi
    rcases (by simpa using hi) with hix | hiy
    · subst i
      exact ⟨by rw [hS, QTripleFamilyThreeData.support]; simp, hxn⟩
    · subst i
      exact ⟨by rw [hS, QTripleFamilyThreeData.support]; simp, hyn⟩

/-- Family 4 has exactly the length-three source and length-two middle as
nonsimple part. -/
theorem nonsimplePart_eq_pair_of_familyFour
    {S : Set ι} (h : σ.QTripleFamilyFour S) :
    ∃ x y : ι, x ≠ y ∧ σ.nonsimplePart S = {x, y} := by
  classical
  obtain ⟨D, hS⟩ := h
  have hxn : ¬ Simple (σ.obj D.x.1) :=
    σ.not_simple_of_compositionLength_eq_three D.x.2.1
  have hmn : ¬ Simple (σ.obj D.chain.middle.index) := by
    intro hsimple
    have hone :=
      (σ.compositionLength_eq_one_iff_simple D.chain.middle.index).2 hsimple
    rw [D.chain.middle.length_two] at hone
    omega
  have hxm : D.x.1 ≠ D.chain.middle.index := by
    intro heq
    have hthree := D.x.2.1
    rw [heq, D.chain.middle.length_two] at hthree
    omega
  refine ⟨D.x.1, D.chain.middle.index, hxm, ?_⟩
  ext i
  constructor
  · rintro ⟨hi, hinsimple⟩
    have hiD : i ∈ D.support := by
      rw [← hS]
      exact hi
    have hi' : i ∈ D.chain.support := by
      simpa [QTripleFamilyFourData.support] using hiD
    rcases (by
        simpa [LengthThreeQuotientChain.support] using hi') with
        hix | him | hib
    · simp [hix]
    · simp [him]
    · exact False.elim
        (hinsimple (by simpa [hib] using D.chain.bottom.simple))
  · intro hi
    rcases (by simpa using hi) with hix | him
    · subst i
      exact ⟨by
        rw [hS, QTripleFamilyFourData.support]
        simp [LengthThreeQuotientChain.support], hxn⟩
    · subst i
      exact ⟨by
        rw [hS, QTripleFamilyFourData.support]
        simp [LengthThreeQuotientChain.support], hmn⟩

/-- Family 5 has exactly its length-three member as nonsimple part. -/
theorem nonsimplePart_eq_singleton_of_familyFive
    {S : Set ι} (h : σ.QTripleFamilyFive S) :
    ∃ x : ι, σ.nonsimplePart S = {x} := by
  classical
  obtain ⟨D, hS⟩ := h
  refine ⟨D.x, ?_⟩
  have hxn : ¬ Simple (σ.obj D.x) :=
    σ.not_simple_of_compositionLength_eq_three D.length_three
  ext i
  constructor
  · rintro ⟨hi, hinsimple⟩
    have hiD : i ∈ D.support := by
      rw [← hS]
      exact hi
    have hi' : i ∈ ({D.x, D.left.index, D.right.index} : Set ι) :=
      by simpa [QTripleFamilyFiveData.support] using hiD
    rcases (by simpa using hi') with hix | hileft | hiright
    · simp [hix]
    · exact False.elim (hinsimple (by simpa [hileft] using D.left.simple))
    · exact False.elim (hinsimple (by simpa [hiright] using D.right.simple))
  · intro hi
    have hix : i = D.x := by simpa using hi
    subst i
    exact ⟨by rw [hS, QTripleFamilyFiveData.support]; simp, hxn⟩

theorem ncard_nonsimplePart_familyOne
    {S : Set ι} (h : σ.QTripleFamilyOne S) :
    (σ.nonsimplePart S).ncard = 0 := by
  rw [σ.nonsimplePart_eq_empty_of_familyOne h]
  simp

theorem ncard_nonsimplePart_familyTwo
    {S : Set ι} (h : σ.QTripleFamilyTwo S) :
    (σ.nonsimplePart S).ncard = 1 := by
  obtain ⟨x, hx⟩ := σ.nonsimplePart_eq_singleton_of_familyTwo h
  rw [hx]
  simp

theorem ncard_nonsimplePart_familyThree
    {S : Set ι} (h : σ.QTripleFamilyThree S) :
    (σ.nonsimplePart S).ncard = 2 := by
  obtain ⟨x, y, hxy, hpart⟩ :=
    σ.nonsimplePart_eq_pair_of_familyThree h
  rw [hpart]
  simp [hxy]

theorem ncard_nonsimplePart_familyFour
    {S : Set ι} (h : σ.QTripleFamilyFour S) :
    (σ.nonsimplePart S).ncard = 2 := by
  obtain ⟨x, y, hxy, hpart⟩ :=
    σ.nonsimplePart_eq_pair_of_familyFour h
  rw [hpart]
  simp [hxy]

theorem ncard_nonsimplePart_familyFive
    {S : Set ι} (h : σ.QTripleFamilyFive S) :
    (σ.nonsimplePart S).ncard = 1 := by
  obtain ⟨x, hx⟩ := σ.nonsimplePart_eq_singleton_of_familyFive h
  rw [hx]
  simp

/-- The one-nonsimple families 2 and 5 cannot overlap: their unique
nonsimple members have composition lengths two and three respectively. -/
theorem familyTwo_disjoint_familyFive
    {S : Set ι} (h₂ : σ.QTripleFamilyTwo S)
    (h₅ : σ.QTripleFamilyFive S) : False := by
  obtain ⟨D₂, hS₂⟩ := h₂
  obtain ⟨D₅, hS₅⟩ := h₅
  have hxmem : D₅.x ∈ S := by
    rw [hS₅, QTripleFamilyFiveData.support]
    simp
  have hxmem' :
      D₅.x ∈ ({D₂.x.1, D₂.top.index, D₂.extra.1} : Set ι) :=
    by
      rw [hS₂, QTripleFamilyTwoData.support] at hxmem
      exact hxmem
  rcases (by simpa using hxmem') with hx | hleft | hright
  · have hthree := D₅.length_three
    rw [hx, D₂.x.2] at hthree
    omega
  · exact
      (σ.not_simple_of_compositionLength_eq_three D₅.length_three)
        (by simpa [hleft] using D₂.top.simple)
  · exact
      (σ.not_simple_of_compositionLength_eq_three D₅.length_three)
        (by simpa [hright] using D₂.extra.2)

/-- The two-nonsimple families 3 and 4 cannot overlap: the family-4 source
has length three whereas both nonsimple family-3 members have length two. -/
theorem familyThree_disjoint_familyFour
    {S : Set ι} (h₃ : σ.QTripleFamilyThree S)
    (h₄ : σ.QTripleFamilyFour S) : False := by
  obtain ⟨D₃, hS₃⟩ := h₃
  obtain ⟨D₄, hS₄⟩ := h₄
  have hxmem : D₄.x.1 ∈ S := by
    rw [hS₄, QTripleFamilyFourData.support]
    simp [LengthThreeQuotientChain.support]
  have hxmem' :
      D₄.x.1 ∈ ({D₃.x.1, D₃.y.1, D₃.x_top.index} : Set ι) :=
    by
      rw [hS₃, QTripleFamilyThreeData.support] at hxmem
      exact hxmem
  rcases (by simpa using hxmem') with hx | hy | htop
  · have hthree := D₄.x.2.1
    rw [hx, D₃.x.2] at hthree
    omega
  · have hthree := D₄.x.2.1
    rw [hy, D₃.y.2] at hthree
    omega
  · exact
      (σ.not_simple_of_compositionLength_eq_three D₄.x.2.1)
        (by simpa [htop] using D₃.x_top.simple)

/-- Names for the five mutually exclusive shape tags. -/
inductive QTripleFamilyKind
  | one | two | three | four | five
  deriving DecidableEq

/-- Membership in one chosen family tag. -/
def IsQTripleFamilyKind (S : Set ι) : QTripleFamilyKind → Prop
  | .one => σ.QTripleFamilyOne S
  | .two => σ.QTripleFamilyTwo S
  | .three => σ.QTripleFamilyThree S
  | .four => σ.QTripleFamilyFour S
  | .five => σ.QTripleFamilyFive S

/-- Number of nonsimple support members forced by a family tag. -/
def QTripleFamilyKind.nonsimpleCount : QTripleFamilyKind → ℕ
  | .one => 0
  | .two => 1
  | .three => 2
  | .four => 2
  | .five => 1

theorem ncard_nonsimplePart_eq_kind_nonsimpleCount
    {S : Set ι} {k : QTripleFamilyKind}
    (h : σ.IsQTripleFamilyKind S k) :
    (σ.nonsimplePart S).ncard = k.nonsimpleCount := by
  cases k with
  | one => exact σ.ncard_nonsimplePart_familyOne h
  | two => exact σ.ncard_nonsimplePart_familyTwo h
  | three => exact σ.ncard_nonsimplePart_familyThree h
  | four => exact σ.ncard_nonsimplePart_familyFour h
  | five => exact σ.ncard_nonsimplePart_familyFive h

/-- A support cannot belong to two different manuscript families.  The
nonsimple count separates all pairs except 2/5 and 3/4; composition length
separates those two remaining pairs. -/
theorem qTripleFamilyKind_unique
    {S : Set ι} {k l : QTripleFamilyKind}
    (hk : σ.IsQTripleFamilyKind S k)
    (hl : σ.IsQTripleFamilyKind S l) :
    k = l := by
  have hkcount :=
    σ.ncard_nonsimplePart_eq_kind_nonsimpleCount hk
  have hlcount :=
    σ.ncard_nonsimplePart_eq_kind_nonsimpleCount hl
  have hcount : k.nonsimpleCount = l.nonsimpleCount :=
    hkcount.symm.trans hlcount
  cases k <;> cases l <;>
    simp_all [QTripleFamilyKind.nonsimpleCount, IsQTripleFamilyKind]
  · exact σ.familyTwo_disjoint_familyFive hk hl
  · exact σ.familyThree_disjoint_familyFour hk hl
  · exact σ.familyThree_disjoint_familyFour hl hk
  · exact σ.familyTwo_disjoint_familyFive hl hk

/-! ## Unconditional consequences of each coarse case -/

/-- A quotient of a selected representative belongs to any quotient-closed
support containing the source. -/
theorem mem_of_epi_of_mem_of_qClosure_isClosed
    {S : Set ι} (hclosed : σ.qClosure.IsClosed S)
    {i j : ι} (hi : i ∈ S)
    (f : σ.obj i ⟶ σ.obj j) [Epi f] :
    j ∈ S := by
  have hjClosure : j ∈ σ.qClosure S := by
    let a : Fin 1 → ι := fun _ ↦ i
    let g :
        σ.sumOver (FintypeCat.of (Fin 1)) a ⟶ σ.obj j :=
      (biproductUniqueIso fun t : Fin 1 ↦ σ.obj (a t)).hom ≫ f
    refine ⟨{
      index := FintypeCat.of (Fin 1)
      label := a
      mem := fun _ ↦ hi
      map := g
      epi := ?_ }⟩
    dsimp only [g]
    infer_instance
  rw [← hclosed.closure_eq]
  exact hjClosure

/-- A representative whose module radical is simple cannot itself be
simple. -/
theorem not_simple_of_moduleRadical_isSimple
    {i : ι} (hrad : IsSimpleModule R (σ.moduleRadical i)) :
    ¬ Simple (σ.obj i) := by
  intro hi
  letI : IsSimpleModule R (σ.obj i) :=
    (simple_iff_isSimpleModule_fg _).mp hi
  letI : IsSemisimpleModule R (σ.obj i) := by infer_instance
  have hbot : σ.moduleRadical i = ⊥ :=
    IsSemisimpleModule.jacobson_eq_bot R (σ.obj i)
  letI : IsSimpleModule R (σ.moduleRadical i) := hrad
  letI : Nontrivial (σ.moduleRadical i) :=
    IsSimpleModule.nontrivial R (σ.moduleRadical i)
  obtain ⟨z, hz⟩ := exists_ne (0 : σ.moduleRadical i)
  apply hz
  apply Subtype.ext
  have hzmemBot :
      (z.1 : σ.obj i) ∈ (⊥ : Submodule R (σ.obj i)) := by
    rw [← hbot]
    exact z.2
  simpa using hzmemBot

/-- In a one-nonsimple closed triple, the unique nonsimple member has simple
module radical.  This follows from the existing simple-radical quotient
construction: its target is selected, cannot be either simple member, and
therefore has the same skeleton index as the source. -/
theorem moduleRadical_isSimple_of_oneNonsimple
    {S : Set ι} (hclosed : σ.qClosure.IsClosed S)
    {x s t : ι} (hS : S = {x, s, t})
    (hxmem : x ∈ S)
    (hss : Simple (σ.obj s)) (hst : Simple (σ.obj t))
    (hxn : ¬ Simple (σ.obj x)) :
    IsSimpleModule R (σ.moduleRadical x) := by
  obtain ⟨j, f, hf, hrad⟩ :=
    OpConjecture.LevelTwoUnconditional.exists_indecomposable_quotient_with_simple_radical
      σ hxn
  letI : Epi f := hf
  have hjmem : j ∈ S :=
    σ.mem_of_epi_of_mem_of_qClosure_isClosed hclosed hxmem f
  rw [hS] at hjmem
  rcases (by simpa using hjmem) with hjx | hjs | hjt
  · subst j
    exact hrad
  · subst j
    exact False.elim
      ((σ.not_simple_of_moduleRadical_isSimple hrad) hss)
  · subst j
    exact False.elim
      ((σ.not_simple_of_moduleRadical_isSimple hrad) hst)

/-- Simple top and simple module radical force composition length two. -/
theorem compositionLength_eq_two_of_moduleTop_isSimple_of_moduleRadical_isSimple
    {i : ι}
    (htop : IsSimpleModule R (σ.moduleTop i))
    (hrad : IsSimpleModule R (σ.moduleRadical i)) :
    σ.compositionLength i = 2 := by
  letI : IsArtinian R (σ.obj i) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (σ.finiteLength i)).2
  letI : IsSimpleModule R (σ.moduleTop i) := htop
  letI : IsSimpleModule R (σ.moduleRadical i) := hrad
  have hiLengthModule : Module.length R (σ.obj i) = 2 := by
    rw [Module.length_eq_add_of_exact
      (σ.moduleRadical i).subtype
      (σ.moduleRadical i).mkQ
      (σ.moduleRadical i).subtype_injective
      (σ.moduleRadical i).mkQ_surjective
      (LinearMap.exact_subtype_mkQ (σ.moduleRadical i)),
      Module.length_eq_one R (σ.moduleRadical i),
      Module.length_eq_one R (σ.moduleTop i)]
    norm_num
  rw [← ENat.coe_inj, σ.coe_compositionLength]
  exact hiLengthModule

/-- The all-simple coarse case is already exactly family 1. -/
theorem familyOne_of_allSimple
    {S : Set ι} (hcard : S.ncard = 3)
    (hsimple : ∀ i ∈ S, Simple (σ.obj i)) :
    σ.QTripleFamilyOne S := by
  obtain ⟨a, b, c, hab, hac, hbc, hS⟩ := Set.ncard_eq_three.mp hcard
  refine ⟨{
    a := a
    b := b
    c := c
    a_ne_b := hab
    a_ne_c := hac
    b_ne_c := hbc
    a_simple := hsimple a (hS.symm ▸ by simp)
    b_simple := hsimple b (hS.symm ▸ by simp)
    c_simple := hsimple c (hS.symm ▸ by simp) }, ?_⟩
  simpa [QTripleFamilyOneData.support] using hS

/-- In the one-nonsimple coarse case, every simple quotient of the nonsimple
member is one of the two displayed simple indices. -/
theorem simpleQuotient_index_eq_left_or_right_of_oneNonsimple
    {S : Set ι} (hclosed : σ.qClosure.IsClosed S)
    {x s t : ι} (hS : S = {x, s, t})
    (hx : x ∈ S)
    (hsx : ¬ Simple (σ.obj x))
    (_hss : Simple (σ.obj s)) (_hst : Simple (σ.obj t))
    (Q : σ.SimpleQuotient x) :
    Q.index = s ∨ Q.index = t := by
  have hQmem : Q.index ∈ S := Q.mem_of_isClosed σ hclosed hx
  rw [hS] at hQmem
  rcases (by simpa using hQmem) with hQx | hQs | hQt
  · exfalso
    apply hsx
    simpa [hQx] using Q.simple
  · exact Or.inl hQs
  · exact Or.inr hQt

/-- The simple-top subcase of the one-nonsimple coarse branch is already
family 2. -/
theorem familyTwo_of_oneNonsimple_of_moduleTop_isSimple
    {S : Set ι} (hclosed : σ.qClosure.IsClosed S)
    {x s t : ι} (_hxs : x ≠ s) (_hxt : x ≠ t) (hst : s ≠ t)
    (hS : S = {x, s, t})
    (hxn : ¬ Simple (σ.obj x))
    (hss : Simple (σ.obj s)) (htt : Simple (σ.obj t))
    (htop : IsSimpleModule R (σ.moduleTop x)) :
    σ.QTripleFamilyTwo S := by
  have hxmem : x ∈ S := by rw [hS]; simp
  have hrad : IsSimpleModule R (σ.moduleRadical x) :=
    σ.moduleRadical_isSimple_of_oneNonsimple
      hclosed hS hxmem hss htt hxn
  have hxlen : σ.compositionLength x = 2 :=
    σ.compositionLength_eq_two_of_moduleTop_isSimple_of_moduleRadical_isSimple
      htop hrad
  let Q := Classical.choice (σ.exists_simpleQuotient x)
  rcases
      σ.simpleQuotient_index_eq_left_or_right_of_oneNonsimple
        hclosed hS hxmem hxn hss htt Q with hQs | hQt
  · refine ⟨{
      x := ⟨x, hxlen⟩
      top := Q
      extra := ⟨t, htt⟩
      extra_ne_top := by simpa [hQs] using hst.symm }, ?_⟩
    simpa [QTripleFamilyTwoData.support, hQs] using hS
  · refine ⟨{
      x := ⟨x, hxlen⟩
      top := Q
      extra := ⟨s, hss⟩
      extra_ne_top := by simpa [hQt] using hst }, ?_⟩
    have hdisplay :
        ({x, Q.index, s} : Set ι) = {x, s, t} := by
      ext i
      simp [hQt, or_comm]
    exact hS.trans hdisplay.symm

/-- If the radical is simple but the top is not, the proved isotypic
Loewy-two classification forces at least two different simple quotient
types. -/
theorem exists_distinct_simpleQuotients_of_not_moduleTop_isSimple_of_moduleRadical_isSimple
    (hclassification :
      OpConjecture.LengthTwoGabrielBridge.IndecomposableSkeleton.IsotypicLoewyTwoIndecomposablesHaveSimpleTop
        σ)
    {x : ι}
    (htop : ¬ IsSimpleModule R (σ.moduleTop x))
    (hrad : IsSimpleModule R (σ.moduleRadical x)) :
    ∃ Q Q' : σ.SimpleQuotient x, Q.index ≠ Q'.index := by
  classical
  by_contra hdistinct
  push Not at hdistinct
  let Q := Classical.choice (σ.exists_simpleQuotient x)
  have hunique : σ.HasUniqueSimpleQuotientType x Q.index :=
    ⟨Q.simple, fun L ↦ hdistinct L Q⟩
  have htopIsotypic :
      IsIsotypicOfType R (σ.moduleTop x) (σ.obj Q.index) :=
    OpConjecture.LevelTwoUnconditional.moduleTop_isIsotypicOfType_of_hasUniqueSimpleQuotientType
      σ hunique
  letI : IsSimpleModule R (σ.moduleRadical x) := hrad
  let Rad : FGModuleCat.{w} R :=
    FGModuleCat.of R (σ.moduleRadical x)
  have hRadIndec : OpConjecture.Foundation.IsIndecomposableModule R Rad :=
    OpConjecture.Foundation.IsSimpleModule.isIndecomposableModule
  obtain ⟨r, ⟨eRad⟩⟩ := σ.complete Rad hRadIndec
  have hRadSimpleCat : Simple Rad :=
    (simple_iff_isSimpleModule_fg Rad).2 inferInstance
  have hrSimple : Simple (σ.obj r) :=
    (Simple.iff_of_iso eRad).mp hRadSimpleCat
  have hradIsotypic :
      IsIsotypicOfType R (σ.moduleRadical x) (σ.obj r) :=
    (IsIsotypicOfType.of_isSimpleModule R
      (σ.moduleRadical x)).of_linearEquiv_type
      (FGModuleCat.isoToLinearEquiv eRad)
  letI : IsSemisimpleModule R (σ.moduleRadical x) := by
    infer_instance
  exact htop
    (hclassification Q.simple hrSimple htopIsotypic
      inferInstance hradIsotypic)

/-- Once the remaining length-three bound is known, the nonsimple-top
subcase of a one-nonsimple closed triple is exactly family 5. -/
theorem familyFive_of_oneNonsimple_of_not_moduleTop_isSimple_of_length_three
    (hclassification :
      OpConjecture.LengthTwoGabrielBridge.IndecomposableSkeleton.IsotypicLoewyTwoIndecomposablesHaveSimpleTop
        σ)
    {S : Set ι} (hclosed : σ.qClosure.IsClosed S)
    {x s t : ι} (_hxs : x ≠ s) (_hxt : x ≠ t) (_hst : s ≠ t)
    (hS : S = {x, s, t})
    (hxn : ¬ Simple (σ.obj x))
    (hss : Simple (σ.obj s)) (htt : Simple (σ.obj t))
    (htop : ¬ IsSimpleModule R (σ.moduleTop x))
    (hxlen : σ.compositionLength x = 3) :
    σ.QTripleFamilyFive S := by
  have hxmem : x ∈ S := by rw [hS]; simp
  have hrad : IsSimpleModule R (σ.moduleRadical x) :=
    σ.moduleRadical_isSimple_of_oneNonsimple
      hclosed hS hxmem hss htt hxn
  obtain ⟨Q, Q', hQQ'⟩ :=
    σ.exists_distinct_simpleQuotients_of_not_moduleTop_isSimple_of_moduleRadical_isSimple
      hclassification htop hrad
  have hQ :=
    σ.simpleQuotient_index_eq_left_or_right_of_oneNonsimple
      hclosed hS hxmem hxn hss htt Q
  have hQ' :=
    σ.simpleQuotient_index_eq_left_or_right_of_oneNonsimple
      hclosed hS hxmem hxn hss htt Q'
  refine ⟨{
    x := x
    length_three := hxlen
    radical_simple := hrad
    left := Q
    right := Q'
    quotient_types_ne := hQQ' }, ?_⟩
  rcases hQ with hQs | hQt <;> rcases hQ' with hQ's | hQ't
  · exact False.elim (hQQ' (hQs.trans hQ's.symm))
  · simpa [QTripleFamilyFiveData.support, hQs, hQ't] using hS
  · have hdisplay :
        ({x, Q.index, Q'.index} : Set ι) = {x, s, t} := by
      ext i
      simp [hQt, hQ's, or_comm]
    exact hS.trans hdisplay.symm
  · exact False.elim (hQQ' (hQt.trans hQ't.symm))

/-- In the two-nonsimple coarse case, every simple quotient of either
nonsimple member is the unique displayed simple index. -/
theorem hasUniqueSimpleQuotientType_of_twoNonsimple
    {S : Set ι} (hclosed : σ.qClosure.IsClosed S)
    {x y s : ι} (hS : S = {x, y, s})
    (hx : x ∈ S) (hy : y ∈ S)
    (hxn : ¬ Simple (σ.obj x)) (hyn : ¬ Simple (σ.obj y))
    (hss : Simple (σ.obj s)) :
    σ.HasUniqueSimpleQuotientType x s ∧
      σ.HasUniqueSimpleQuotientType y s := by
  constructor
  · refine ⟨hss, ?_⟩
    intro Q
    have hQmem : Q.index ∈ S := Q.mem_of_isClosed σ hclosed hx
    rw [hS] at hQmem
    rcases (by simpa using hQmem) with hQx | hQy | hQs
    · exfalso
      apply hxn
      simpa [hQx] using Q.simple
    · exfalso
      apply hyn
      simpa [hQy] using Q.simple
    · exact hQs
  · refine ⟨hss, ?_⟩
    intro Q
    have hQmem : Q.index ∈ S := Q.mem_of_isClosed σ hclosed hy
    rw [hS] at hQmem
    rcases (by simpa using hQmem) with hQx | hQy | hQs
    · exfalso
      apply hxn
      simpa [hQx] using Q.simple
    · exfalso
      apply hyn
      simpa [hQy] using Q.simple
    · exact hQs

/-- Under the proved isotypic Loewy-two theorem, a representative with one
simple quotient type and simple radical has composition length two. -/
theorem compositionLength_eq_two_of_hasUniqueSimpleQuotientType_of_moduleRadical_isSimple
    (hclassification :
      OpConjecture.LengthTwoGabrielBridge.IndecomposableSkeleton.IsotypicLoewyTwoIndecomposablesHaveSimpleTop
        σ)
    {j s : ι}
    (hunique : σ.HasUniqueSimpleQuotientType j s)
    (hrad : IsSimpleModule R (σ.moduleRadical j)) :
    σ.compositionLength j = 2 := by
  have htopIsotypic :
      IsIsotypicOfType R (σ.moduleTop j) (σ.obj s) :=
    OpConjecture.LevelTwoUnconditional.moduleTop_isIsotypicOfType_of_hasUniqueSimpleQuotientType
      σ hunique
  letI : IsSimpleModule R (σ.moduleRadical j) := hrad
  let Rad : FGModuleCat.{w} R :=
    FGModuleCat.of R (σ.moduleRadical j)
  have hRadIndec : OpConjecture.Foundation.IsIndecomposableModule R Rad :=
    OpConjecture.Foundation.IsSimpleModule.isIndecomposableModule
  obtain ⟨r, ⟨eRad⟩⟩ := σ.complete Rad hRadIndec
  have hRadSimpleCat : Simple Rad :=
    (simple_iff_isSimpleModule_fg Rad).2 inferInstance
  have hrSimple : Simple (σ.obj r) :=
    (Simple.iff_of_iso eRad).mp hRadSimpleCat
  have hradIsotypic :
      IsIsotypicOfType R (σ.moduleRadical j) (σ.obj r) :=
    (IsIsotypicOfType.of_isSimpleModule R
      (σ.moduleRadical j)).of_linearEquiv_type
      (FGModuleCat.isoToLinearEquiv eRad)
  letI : IsSemisimpleModule R (σ.moduleRadical j) := by
    infer_instance
  have htop : IsSimpleModule R (σ.moduleTop j) :=
    hclassification hunique.1 hrSimple htopIsotypic
      inferInstance hradIsotypic
  exact
    σ.compositionLength_eq_two_of_moduleTop_isSimple_of_moduleRadical_isSimple
      htop hrad

/-- In the two-nonsimple coarse branch, at least one nonsimple member has
composition length two.  Take the existing indecomposable quotient with
simple radical; closedness keeps it in the three-support, and the unique
simple quotient type plus the isotypic Loewy-two theorem forces length two. -/
theorem length_two_left_or_right_of_twoNonsimple
    (hclassification :
      OpConjecture.LengthTwoGabrielBridge.IndecomposableSkeleton.IsotypicLoewyTwoIndecomposablesHaveSimpleTop
        σ)
    {S : Set ι} (hclosed : σ.qClosure.IsClosed S)
    {x y s : ι} (hS : S = {x, y, s})
    (hxn : ¬ Simple (σ.obj x)) (hyn : ¬ Simple (σ.obj y))
    (hss : Simple (σ.obj s)) :
    σ.compositionLength x = 2 ∨
      σ.compositionLength y = 2 := by
  have hxmem : x ∈ S := by rw [hS]; simp
  have hymem : y ∈ S := by rw [hS]; simp
  have hunique :=
    σ.hasUniqueSimpleQuotientType_of_twoNonsimple
      hclosed hS hxmem hymem hxn hyn hss
  obtain ⟨j, f, hf, hrad⟩ :=
    OpConjecture.LevelTwoUnconditional.exists_indecomposable_quotient_with_simple_radical
      σ hxn
  letI : Epi f := hf
  have hjmem : j ∈ S :=
    σ.mem_of_epi_of_mem_of_qClosure_isClosed hclosed hxmem f
  rw [hS] at hjmem
  rcases (by simpa using hjmem) with hjx | hjy | hjs
  · subst j
    exact Or.inl
      (σ.compositionLength_eq_two_of_hasUniqueSimpleQuotientType_of_moduleRadical_isSimple
        hclassification hunique.1 hrad)
  · subst j
    exact Or.inr
      (σ.compositionLength_eq_two_of_hasUniqueSimpleQuotientType_of_moduleRadical_isSimple
        hclassification hunique.2 hrad)
  · subst j
    exact False.elim
      ((σ.not_simple_of_moduleRadical_isSimple hrad) hss)

/-- If both nonsimple members in the two-nonsimple coarse case have length
two, the support is exactly family 3. -/
theorem familyThree_of_twoNonsimple_of_lengths_two
    {S : Set ι} (hclosed : σ.qClosure.IsClosed S)
    {x y s : ι} (hxy : x ≠ y)
    (hS : S = {x, y, s})
    (hxn : ¬ Simple (σ.obj x)) (hyn : ¬ Simple (σ.obj y))
    (hss : Simple (σ.obj s))
    (hxlen : σ.compositionLength x = 2)
    (hylen : σ.compositionLength y = 2) :
    σ.QTripleFamilyThree S := by
  have hxmem : x ∈ S := hS.symm ▸ by simp
  have hymem : y ∈ S := hS.symm ▸ by simp
  have hunique :=
    σ.hasUniqueSimpleQuotientType_of_twoNonsimple hclosed hS
      hxmem hymem hxn hyn hss
  let Qx := Classical.choice (σ.exists_simpleQuotient x)
  let Qy := Classical.choice (σ.exists_simpleQuotient y)
  have hQx : Qx.index = s := hunique.1.2 Qx
  have hQy : Qy.index = s := hunique.2.2 Qy
  refine ⟨{
    x := ⟨x, hxlen⟩
    y := ⟨y, hylen⟩
    x_ne_y := fun h ↦ hxy (congrArg Subtype.val h)
    x_top := Qx
    y_top := Qy
    same_top := hQx.trans hQy.symm }, ?_⟩
  simpa [QTripleFamilyThreeData.support, hQx] using hS

/-- A closed support containing a length-three uniserial member is exactly
the canonical quotient-chain support as soon as it has cardinality three.
This direction uses no collective-closure assertion for arbitrary uniserial
chains: closedness is an input. -/
theorem familyFour_of_mem_isLengthThreeUniserial
    {S : Set ι} (hcard : S.ncard = 3)
    (hclosed : σ.qClosure.IsClosed S)
    {x : ι} (hxmem : x ∈ S)
    (hx : σ.IsLengthThreeUniserial x) :
    σ.QTripleFamilyFour S := by
  let xu : σ.LengthThreeUniserialIndex := ⟨x, hx⟩
  let C := σ.lengthThreeQuotientChain xu
  have hsubset : C.support ⊆ S := by
    intro j hj
    obtain ⟨f, hf⟩ := C.exists_epi_to_mem_support σ hj
    letI : Epi f := hf
    have hjClosure : j ∈ σ.qClosure S := by
      let a : Fin 1 → ι := fun _ ↦ x
      let g :
          σ.sumOver (FintypeCat.of (Fin 1)) a ⟶ σ.obj j :=
        (biproductUniqueIso fun t : Fin 1 ↦ σ.obj (a t)).hom ≫ f
      refine ⟨{
        index := FintypeCat.of (Fin 1)
        label := a
        mem := fun _ ↦ hxmem
        map := g
        epi := ?_ }⟩
      dsimp only [g]
      infer_instance
    rw [← hclosed.closure_eq]
    exact hjClosure
  have hSfinite : S.Finite :=
    Set.finite_of_ncard_ne_zero (by omega)
  have hsupport : C.support = S :=
    Set.eq_of_subset_of_ncard_le hsubset (by
      rw [hcard, C.ncard_support]) hSfinite
  refine ⟨{
    x := xu
    chain := C }, ?_⟩
  simpa [QTripleFamilyFourData.support] using hsupport.symm

/-! ## Sufficient remaining local refinements -/

/-- The genuinely missing assertion in the one-nonsimple branch after all
currently compiled consequences: if its top is not simple, then the unique
nonsimple member has composition length three. -/
def OneNonsimpleLengthThreeControl : Prop :=
  ∀ {S : Set ι}, S.ncard = 3 → σ.qClosure.IsClosed S →
    ∀ {x s t : ι},
      x ≠ s → x ≠ t → s ≠ t →
      S = {x, s, t} →
      ¬ Simple (σ.obj x) →
      Simple (σ.obj s) → Simple (σ.obj t) →
      ¬ IsSimpleModule R (σ.moduleTop x) →
      σ.compositionLength x = 3

/-- The genuinely missing assertion in the two-nonsimple branch after one
member is known to have length two: any member which is not length two is a
length-three uniserial module. -/
def TwoNonsimpleLongUniserialControl : Prop :=
  ∀ {S : Set ι}, S.ncard = 3 → σ.qClosure.IsClosed S →
    ∀ {x y s : ι},
      x ≠ y → x ≠ s → y ≠ s →
      S = {x, y, s} →
      ¬ Simple (σ.obj x) → ¬ Simple (σ.obj y) →
      Simple (σ.obj s) →
      (σ.compositionLength x ≠ 2 → σ.IsLengthThreeUniserial x) ∧
        (σ.compositionLength y ≠ 2 → σ.IsLengthThreeUniserial y)

/-- The remaining local theorem in the coarse one-nonsimple branch.  It says
that the unique nonsimple member is either a length-two module (family 2) or
the branched length-three module (family 5). -/
def OneNonsimpleRefinement : Prop :=
  ∀ {S : Set ι}, S.ncard = 3 → σ.qClosure.IsClosed S →
    ∀ {x s t : ι},
      x ≠ s → x ≠ t → s ≠ t →
      S = {x, s, t} →
      ¬ Simple (σ.obj x) →
      Simple (σ.obj s) → Simple (σ.obj t) →
      σ.QTripleFamilyTwo S ∨ σ.QTripleFamilyFive S

/-- The remaining local theorem in the coarse two-nonsimple branch.  It says
that the two nonsimple members either both have length two (family 3), or one
is a length-three uniserial source whose quotient chain is the support
(family 4). -/
def TwoNonsimpleRefinement : Prop :=
  ∀ {S : Set ι}, S.ncard = 3 → σ.qClosure.IsClosed S →
    ∀ {x y s : ι},
      x ≠ y → x ≠ s → y ≠ s →
      S = {x, y, s} →
      ¬ Simple (σ.obj x) → ¬ Simple (σ.obj y) →
      Simple (σ.obj s) →
      σ.QTripleFamilyThree S ∨ σ.QTripleFamilyFour S

/-- The proved isotypic Loewy-two theorem and the sole remaining length bound
construct the complete one-nonsimple refinement. -/
theorem oneNonsimpleRefinement_of_lengthThreeControl
    (hclassification :
      OpConjecture.LengthTwoGabrielBridge.IndecomposableSkeleton.IsotypicLoewyTwoIndecomposablesHaveSimpleTop
        σ)
    (hlength : σ.OneNonsimpleLengthThreeControl) :
    σ.OneNonsimpleRefinement := by
  intro S hcard hclosed x s t hxs hxt hst hS hxn hss htt
  by_cases htop : IsSimpleModule R (σ.moduleTop x)
  · exact Or.inl
      (σ.familyTwo_of_oneNonsimple_of_moduleTop_isSimple
        hclosed hxs hxt hst hS hxn hss htt htop)
  · have hxlen : σ.compositionLength x = 3 :=
      hlength hcard hclosed hxs hxt hst hS hxn hss htt htop
    exact Or.inr
      (σ.familyFive_of_oneNonsimple_of_not_moduleTop_isSimple_of_length_three
        hclassification hclosed hxs hxt hst hS hxn hss htt htop hxlen)

/-- The proved existence of a length-two member and the sole remaining
long-chain assertion construct the complete two-nonsimple refinement. -/
theorem twoNonsimpleRefinement_of_longUniserialControl
    (hclassification :
      OpConjecture.LengthTwoGabrielBridge.IndecomposableSkeleton.IsotypicLoewyTwoIndecomposablesHaveSimpleTop
        σ)
    (hlong : σ.TwoNonsimpleLongUniserialControl) :
    σ.TwoNonsimpleRefinement := by
  intro S hcard hclosed x y s hxy hxs hys hS hxn hyn hss
  have hcontrol :=
    hlong hcard hclosed hxy hxs hys hS hxn hyn hss
  have honeLength :=
    σ.length_two_left_or_right_of_twoNonsimple
      hclassification hclosed hS hxn hyn hss
  by_cases hxlen : σ.compositionLength x = 2
  · by_cases hylen : σ.compositionLength y = 2
    · exact Or.inl
        (σ.familyThree_of_twoNonsimple_of_lengths_two
          hclosed hxy hS hxn hyn hss hxlen hylen)
    · have hyUniserial : σ.IsLengthThreeUniserial y :=
        hcontrol.2 hylen
      have hymem : y ∈ S := by rw [hS]; simp
      exact Or.inr
        (σ.familyFour_of_mem_isLengthThreeUniserial
          hcard hclosed hymem hyUniserial)
  · have hylen : σ.compositionLength y = 2 :=
      honeLength.resolve_left hxlen
    have hxUniserial : σ.IsLengthThreeUniserial x :=
      hcontrol.1 hxlen
    have hxmem : x ∈ S := by rw [hS]; simp
    exact Or.inr
      (σ.familyFour_of_mem_isLengthThreeUniserial
        hcard hclosed hxmem hxUniserial)

/-- The two precise local refinements, together with the unconditional coarse
partition, imply quotient-side exhaustiveness of the five manuscript
families. -/
theorem qClosedTriple_five_family_exhaustive
    (hone : σ.OneNonsimpleRefinement)
    (htwo : σ.TwoNonsimpleRefinement)
    {S : Set ι} (hcard : S.ncard = 3)
    (hclosed : σ.qClosure.IsClosed S) :
    σ.QTripleFamily S := by
  cases σ.qClosedTriple_coarse_exhaustive hcard hclosed with
  | allSimple hsimple =>
      exact .one (σ.familyOne_of_allSimple hcard hsimple)
  | oneNonsimple x s t hxs hxt hst hS hxn hss htt =>
      rcases hone hcard hclosed hxs hxt hst hS hxn hss htt with h | h
      · exact .two h
      · exact .five h
  | twoNonsimple x y s hxy hxs hys hS hxn hyn hss =>
      rcases htwo hcard hclosed hxy hxs hys hS hxn hyn hss with h | h
      · exact .three h
      · exact .four h

/-- Quotient-side exhaustiveness endpoint: under the two isolated local
refinements, every quotient-closed support of cardinality three has a unique
numbered manuscript-family kind.  This does not assert uniqueness of the
data witnessing that kind or the converse closure of every listed support. -/
theorem qClosedTriple_existsUnique_familyKind
    (hone : σ.OneNonsimpleRefinement)
    (htwo : σ.TwoNonsimpleRefinement)
    {S : Set ι} (hcard : S.ncard = 3)
    (hclosed : σ.qClosure.IsClosed S) :
    ∃! k : QTripleFamilyKind, σ.IsQTripleFamilyKind S k := by
  rcases σ.qClosedTriple_five_family_exhaustive
      hone htwo hcard hclosed with h | h | h | h | h
  · refine ⟨.one, h, ?_⟩
    intro k hk
    exact σ.qTripleFamilyKind_unique hk h
  · refine ⟨.two, h, ?_⟩
    intro k hk
    exact σ.qTripleFamilyKind_unique hk h
  · refine ⟨.three, h, ?_⟩
    intro k hk
    exact σ.qTripleFamilyKind_unique hk h
  · refine ⟨.four, h, ?_⟩
    intro k hk
    exact σ.qTripleFamilyKind_unique hk h
  · refine ⟨.five, h, ?_⟩
    intro k hk
    exact σ.qTripleFamilyKind_unique hk h

/-- Consolidated endpoint after using the already-proved isotypic Loewy-two
classification: only the two explicitly named long-module controls remain. -/
theorem qClosedTriple_existsUnique_familyKind_of_longControls
    (hclassification :
      OpConjecture.LengthTwoGabrielBridge.IndecomposableSkeleton.IsotypicLoewyTwoIndecomposablesHaveSimpleTop
        σ)
    (hone : σ.OneNonsimpleLengthThreeControl)
    (htwo : σ.TwoNonsimpleLongUniserialControl)
    {S : Set ι} (hcard : S.ncard = 3)
    (hclosed : σ.qClosure.IsClosed S) :
    ∃! k : QTripleFamilyKind, σ.IsQTripleFamilyKind S k :=
  σ.qClosedTriple_existsUnique_familyKind
    (σ.oneNonsimpleRefinement_of_lengthThreeControl
      hclassification hone)
    (σ.twoNonsimpleRefinement_of_longUniserialControl
      hclassification htwo)
    hcard hclosed

end OpConjecture.IndecomposableSkeleton
