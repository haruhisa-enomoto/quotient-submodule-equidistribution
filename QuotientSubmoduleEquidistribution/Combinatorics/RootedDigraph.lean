import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.Logic.Relation

/-!
# Rooted deletion sets in a finite directed graph

This file formalizes the graph-theoretic definition used in
`paper/quotient_submodule_equidistribution/level-four.tex`.  Although the intended vertex type
is finite, the proof only needs the selected vertex sets themselves to be
finite, so the statements are formulated for `Finset`s in an arbitrary
vertex type.
-/

noncomputable section

namespace QuotientSubmoduleEquidistribution.RootedDigraph

universe u

variable {Vertex : Type u} [DecidableEq Vertex]

/-- An edge whose two endpoints both lie in the selected vertex set. -/
def InsideEdge
    (edge : Vertex → Vertex → Prop) (D : Finset Vertex)
    (x y : Vertex) : Prop :=
  x ∈ D ∧ y ∈ D ∧ edge x y

/-- Reachability by an oriented path all of whose vertices lie in `D`.
The reflexive path is allowed. -/
def ReachInside
    (edge : Vertex → Vertex → Prop) (D : Finset Vertex)
    (x y : Vertex) : Prop :=
  Relation.ReflTransGen (InsideEdge edge D) x y

omit [DecidableEq Vertex] in
/-- Reachability is monotone under enlarging the induced vertex set. -/
theorem reachInside_mono
    {edge : Vertex → Vertex → Prop}
    {S D : Finset Vertex}
    (hSD : S ⊆ D)
    {x y : Vertex}
    (hxy : ReachInside edge S x y) :
    ReachInside edge D x y := by
  have hrel :
      InsideEdge edge S ≤ InsideEdge edge D := by
    intro u v huv
    exact
      ⟨hSD huv.1, hSD huv.2.1, huv.2.2⟩
  exact
    Relation.ReflTransGen.mono hrel x y hxy

/-- A vertex is reached inside `D` from a selected boundary vertex. -/
def ReachedFromBoundary
    (edge : Vertex → Vertex → Prop)
    (P D : Finset Vertex) (x : Vertex) : Prop :=
  ∃ p : Vertex,
    p ∈ P ∧ p ∈ D ∧ ReachInside edge D p x

/-- Every vertex of `D` is reached inside `D` from `P ∩ D`.

For the Auslander--Reiten application, `P` is the set of projective
vertices. -/
def IsProjectivelyRooted
    (edge : Vertex → Vertex → Prop)
    (P D : Finset Vertex) : Prop :=
  ∀ x ∈ D, ReachedFromBoundary edge P D x

/-- The vertices of `D` which are not reached from `P ∩ D`. -/
def unreachableVertices
    (edge : Vertex → Vertex → Prop)
    (P D : Finset Vertex) : Finset Vertex :=
  by
    classical
    exact D.filter fun x ↦
      ¬ ReachedFromBoundary edge P D x

omit [DecidableEq Vertex] in
@[simp]
theorem mem_unreachableVertices
    {edge : Vertex → Vertex → Prop}
    {P D : Finset Vertex} {x : Vertex} :
    x ∈ unreachableVertices edge P D ↔
      x ∈ D ∧ ¬ ReachedFromBoundary edge P D x := by
  classical
  simp [unreachableVertices]

/-- A top part of `D`: a nonempty set of nonboundary vertices with no
edge entering it from the rest of `D`. -/
def IsTopPart
    (edge : Vertex → Vertex → Prop)
    (P D S : Finset Vertex) : Prop :=
  S.Nonempty ∧
    S ⊆ D \ P ∧
    ∀ u ∈ D \ S, ∀ v ∈ S, ¬ edge u v

/-- Inclusion-minimality among top parts of the same selected set. -/
def IsMinimalTopPart
    (edge : Vertex → Vertex → Prop)
    (P D S : Finset Vertex) : Prop :=
  IsTopPart edge P D S ∧
    ∀ T : Finset Vertex,
      IsTopPart edge P D T →
        T ⊆ S → S ⊆ T

/-- Every top part contains an inclusion-minimal top part.  This is the
finite-descent step which makes minimal top parts available without any
ambient finiteness assumption on the vertex type. -/
theorem exists_isMinimalTopPart_subset
    {edge : Vertex → Vertex → Prop}
    {P D S : Finset Vertex}
    (hS : IsTopPart edge P D S) :
    ∃ T : Finset Vertex,
      IsMinimalTopPart edge P D T ∧ T ⊆ S := by
  obtain ⟨T, hTS, hTminimal⟩ :=
    exists_minimal_le_of_wellFoundedLT
      (fun T : Finset Vertex ↦ IsTopPart edge P D T)
      S hS
  exact ⟨T, hTminimal, hTS⟩

/-- Strong connectivity in the subgraph induced by `S`. -/
def IsStronglyConnectedInside
    (edge : Vertex → Vertex → Prop)
    (S : Finset Vertex) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S,
    ReachInside edge S x y

/-- The intersection of two intersecting top parts is again a top
part. -/
theorem isTopPart_inter
    {edge : Vertex → Vertex → Prop}
    {P D S T : Finset Vertex}
    (hS : IsTopPart edge P D S)
    (hT : IsTopPart edge P D T)
    (hne : (S ∩ T).Nonempty) :
    IsTopPart edge P D (S ∩ T) := by
  refine ⟨hne, ?_, ?_⟩
  · exact Finset.inter_subset_left.trans hS.2.1
  · intro u hu v hv huv
    have huD :=
      (Finset.mem_sdiff.mp hu).1
    have hvData :=
      Finset.mem_inter.mp hv
    by_cases huS : u ∈ S
    · have huT : u ∉ T := by
        intro huT
        exact
          (Finset.mem_sdiff.mp hu).2
            (Finset.mem_inter.mpr ⟨huS, huT⟩)
      exact
        hT.2.2 u
          (Finset.mem_sdiff.mpr ⟨huD, huT⟩)
          v hvData.2 huv
    · exact
        hS.2.2 u
          (Finset.mem_sdiff.mpr ⟨huD, huS⟩)
          v hvData.1 huv

/-- The union of two top parts of the same selected set is again a top
part. -/
theorem isTopPart_union
    {edge : Vertex → Vertex → Prop}
    {P D S T : Finset Vertex}
    (hS : IsTopPart edge P D S)
    (hT : IsTopPart edge P D T) :
    IsTopPart edge P D (S ∪ T) := by
  refine ⟨hS.1.mono Finset.subset_union_left, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with hxS | hxT
    · exact hS.2.1 hxS
    · exact hT.2.1 hxT
  · intro u hu v hv huv
    have huData := Finset.mem_sdiff.mp hu
    have huS : u ∉ S := by
      intro huS
      exact huData.2 (Finset.mem_union_left T huS)
    have huT : u ∉ T := by
      intro huT
      exact huData.2 (Finset.mem_union_right S huT)
    rcases Finset.mem_union.mp hv with hvS | hvT
    · exact
        hS.2.2 u
          (Finset.mem_sdiff.mpr ⟨huData.1, huS⟩)
          v hvS huv
    · exact
        hT.2.2 u
          (Finset.mem_sdiff.mpr ⟨huData.1, huT⟩)
          v hvT huv

/-- Two minimal top parts which intersect are equal. -/
theorem eq_of_minimalTopParts_of_inter_nonempty
    {edge : Vertex → Vertex → Prop}
    {P D S T : Finset Vertex}
    (hS : IsMinimalTopPart edge P D S)
    (hT : IsMinimalTopPart edge P D T)
    (hne : (S ∩ T).Nonempty) :
    S = T := by
  have hInter :=
    isTopPart_inter hS.1 hT.1 hne
  have hSInter :
      S ⊆ S ∩ T :=
    hS.2 (S ∩ T) hInter
      Finset.inter_subset_left
  have hTInter :
      T ⊆ S ∩ T :=
    hT.2 (S ∩ T) hInter
      Finset.inter_subset_right
  apply Finset.Subset.antisymm
  · exact fun x hxS ↦
      (Finset.mem_inter.mp (hSInter hxS)).2
  · exact fun x hxT ↦
      (Finset.mem_inter.mp (hTInter hxT)).1

/-- Distinct minimal top parts are disjoint. -/
theorem eq_or_disjoint_of_minimalTopParts
    {edge : Vertex → Vertex → Prop}
    {P D S T : Finset Vertex}
    (hS : IsMinimalTopPart edge P D S)
    (hT : IsMinimalTopPart edge P D T) :
    S = T ∨ Disjoint S T := by
  rcases Finset.disjoint_or_nonempty_inter S T with
    hdisjoint | hinter
  · exact Or.inr hdisjoint
  · exact Or.inl
      (eq_of_minimalTopParts_of_inter_nonempty
        hS hT hinter)

/-- Vertices of `S` from which `y` is reachable inside `S`. -/
def ancestorsInside
    (edge : Vertex → Vertex → Prop)
    (S : Finset Vertex) (y : Vertex) :
    Finset Vertex :=
  by
    classical
    exact
      S.filter fun x ↦ ReachInside edge S x y

omit [DecidableEq Vertex] in
@[simp]
theorem mem_ancestorsInside
    {edge : Vertex → Vertex → Prop}
    {S : Finset Vertex} {x y : Vertex} :
    x ∈ ancestorsInside edge S y ↔
      x ∈ S ∧ ReachInside edge S x y := by
  classical
  simp [ancestorsInside]

/-- Every minimal top part is strongly connected in its induced
subgraph. -/
theorem isStronglyConnectedInside_of_isMinimalTopPart
    {edge : Vertex → Vertex → Prop}
    {P D S : Finset Vertex}
    (hS : IsMinimalTopPart edge P D S) :
    IsStronglyConnectedInside edge S := by
  rw [IsStronglyConnectedInside]
  by_contra hnotStrong
  push Not at hnotStrong
  obtain ⟨x, hxS, y, hyS, hxy⟩ :=
    hnotStrong
  let T := ancestorsInside edge S y
  have hTtop :
      IsTopPart edge P D T := by
    refine ⟨?_, ?_, ?_⟩
    · exact
        ⟨y, (mem_ancestorsInside
          (edge := edge) (S := S)).2
            ⟨hyS, Relation.ReflTransGen.refl⟩⟩
    · intro z hzT
      exact
        hS.1.2.1
          ((mem_ancestorsInside
            (edge := edge) (S := S)).1 hzT).1
    · intro u hu v hv huv
      have huD :=
        (Finset.mem_sdiff.mp hu).1
      have hvData :=
        (mem_ancestorsInside
          (edge := edge) (S := S)).1 hv
      by_cases huS : u ∈ S
      · have huvInside :
            InsideEdge edge S u v :=
          ⟨huS, hvData.1, huv⟩
        have huy :
            ReachInside edge S u y :=
          Relation.ReflTransGen.head
            huvInside hvData.2
        exact
          (Finset.mem_sdiff.mp hu).2
            ((mem_ancestorsInside
              (edge := edge) (S := S)).2
                ⟨huS, huy⟩)
      · exact
          hS.1.2.2 u
            (Finset.mem_sdiff.mpr ⟨huD, huS⟩)
            v hvData.1 huv
  have hST : S ⊆ T :=
    hS.2 T hTtop (by
      intro z hzT
      exact
        ((mem_ancestorsInside
          (edge := edge) (S := S)).1 hzT).1)
  have hxT :=
    (mem_ancestorsInside
      (edge := edge) (S := S)).1
      (hST hxS)
  exact hxy hxT.2

/-- The union of a finite family of vertex supports. -/
def supportFamilyUnion
    (T : Finset (Finset Vertex)) : Finset Vertex :=
  T.biUnion id

/-- The union of a nonempty finite family of top parts is a top part. -/
theorem isTopPart_supportFamilyUnion
    {edge : Vertex → Vertex → Prop}
    {P D : Finset Vertex}
    {C : Finset (Finset Vertex)}
    (hC : C.Nonempty)
    (hTop :
      ∀ S ∈ C, IsTopPart edge P D S) :
    IsTopPart edge P D (supportFamilyUnion C) := by
  classical
  induction C using Finset.induction_on with
  | empty =>
      exact (Finset.not_nonempty_empty hC).elim
  | @insert S C hSC ih =>
      by_cases hCempty : C = ∅
      · subst C
        simpa [supportFamilyUnion] using
          hTop S (Finset.mem_singleton_self S)
      · have hCTop :
            IsTopPart edge P D
              (supportFamilyUnion C) :=
          ih (Finset.nonempty_iff_ne_empty.mpr hCempty)
            (fun T hTC ↦
              hTop T (Finset.mem_insert_of_mem hTC))
        have hSTop :
            IsTopPart edge P D S :=
          hTop S (Finset.mem_insert_self S C)
        simpa [supportFamilyUnion] using
          isTopPart_union hSTop hCTop

/-- The canonical finite family of all minimal top parts of `D`. -/
def minimalTopParts
    (edge : Vertex → Vertex → Prop)
    (P D : Finset Vertex) :
    Finset (Finset Vertex) :=
  by
    classical
    exact
      D.powerset.filter fun S ↦
        IsMinimalTopPart edge P D S

@[simp]
theorem mem_minimalTopParts
    {edge : Vertex → Vertex → Prop}
    {P D S : Finset Vertex} :
    S ∈ minimalTopParts edge P D ↔
      IsMinimalTopPart edge P D S := by
  classical
  rw [minimalTopParts, Finset.mem_filter,
    Finset.mem_powerset]
  constructor
  · exact And.right
  · intro hS
    exact
      ⟨hS.1.2.1.trans Finset.sdiff_subset,
        hS⟩

/-- A finite family of nonempty, pairwise-disjoint supports. -/
def IsDisjointNonemptySupportFamily
    (C : Finset (Finset Vertex)) : Prop :=
  (∀ S ∈ C, S.Nonempty) ∧
    ∀ S ∈ C, ∀ T ∈ C, S ≠ T →
      Disjoint S T

/-- Any finite family of minimal top parts of a fixed selected set is a
family of nonempty, pairwise-disjoint supports. -/
theorem isDisjointNonemptySupportFamily_of_minimalTopParts
    {edge : Vertex → Vertex → Prop}
    {P D : Finset Vertex}
    {C : Finset (Finset Vertex)}
    (hminimal :
      ∀ S ∈ C,
        IsMinimalTopPart edge P D S) :
    IsDisjointNonemptySupportFamily C := by
  constructor
  · intro S hSC
    exact (hminimal S hSC).1.1
  · intro S hSC T hTC hST
    rcases
      eq_or_disjoint_of_minimalTopParts
        (hminimal S hSC) (hminimal T hTC) with
      heq | hdisjoint
    · exact (hST heq).elim
    · exact hdisjoint

/-- The canonical family of all minimal top parts of `D` is nonempty
supportwise and pairwise disjoint. -/
theorem isDisjointNonemptySupportFamily_minimalTopParts
    (edge : Vertex → Vertex → Prop)
    (P D : Finset Vertex) :
    IsDisjointNonemptySupportFamily
      (minimalTopParts edge P D) := by
  apply
    isDisjointNonemptySupportFamily_of_minimalTopParts
  intro S hS
  exact
    (mem_minimalTopParts
      (edge := edge) (P := P) (D := D)).1 hS

/-- A component-separated support family: its members are nonempty and
pairwise disjoint, and no edge joins two distinct members.  Since the
last condition is quantified over ordered pairs, it excludes edges in
both directions. -/
def IsSeparatedSupportFamily
    (edge : Vertex → Vertex → Prop)
    (C : Finset (Finset Vertex)) : Prop :=
  IsDisjointNonemptySupportFamily C ∧
    ∀ S ∈ C, ∀ T ∈ C, S ≠ T →
      ∀ x ∈ S, ∀ y ∈ T, ¬ edge x y

omit [DecidableEq Vertex] in
/-- A subfamily of a separated support family is separated. -/
theorem IsSeparatedSupportFamily.mono
    {edge : Vertex → Vertex → Prop}
    {C T : Finset (Finset Vertex)}
    (hC : IsSeparatedSupportFamily edge C)
    (hTC : T ⊆ C) :
    IsSeparatedSupportFamily edge T := by
  constructor
  · constructor
    · intro S hST
      exact hC.1.1 S (hTC hST)
    · intro S hST U hUT hSU
      exact
        hC.1.2 S (hTC hST) U (hTC hUT) hSU
  · intro S hST U hUT hSU
    exact
      hC.2 S (hTC hST) U (hTC hUT) hSU

/-- Any finite family of minimal top parts of one selected set is
component-separated. -/
theorem isSeparatedSupportFamily_of_minimalTopParts
    {edge : Vertex → Vertex → Prop}
    {P D : Finset Vertex}
    {C : Finset (Finset Vertex)}
    (hminimal :
      ∀ S ∈ C,
        IsMinimalTopPart edge P D S) :
    IsSeparatedSupportFamily edge C := by
  have hDisjoint :=
    isDisjointNonemptySupportFamily_of_minimalTopParts
      hminimal
  refine ⟨hDisjoint, ?_⟩
  intro S hSC T hTC hST x hxS y hyT hxy
  have hxD :
      x ∈ D :=
    (Finset.mem_sdiff.mp
      ((hminimal S hSC).1.2.1 hxS)).1
  have hxT : x ∉ T := by
    intro hxT
    exact
      (Finset.disjoint_left.mp
        (hDisjoint.2 S hSC T hTC hST))
        hxS hxT
  exact
    (hminimal T hTC).1.2.2 x
      (Finset.mem_sdiff.mpr ⟨hxD, hxT⟩)
      y hyT hxy

/-- The canonical family of all minimal top parts is
component-separated. -/
theorem isSeparatedSupportFamily_minimalTopParts
    (edge : Vertex → Vertex → Prop)
    (P D : Finset Vertex) :
    IsSeparatedSupportFamily edge
      (minimalTopParts edge P D) := by
  apply isSeparatedSupportFamily_of_minimalTopParts
  intro S hS
  exact
    (mem_minimalTopParts
      (edge := edge) (P := P) (D := D)).1 hS

/-- For a nonempty separated family, its union is a top part exactly
when every component is a top part. -/
theorem isTopPart_supportFamilyUnion_iff
    {edge : Vertex → Vertex → Prop}
    {P D : Finset Vertex}
    {C : Finset (Finset Vertex)}
    (hC : C.Nonempty)
    (hSeparated :
      IsSeparatedSupportFamily edge C) :
    IsTopPart edge P D (supportFamilyUnion C) ↔
      ∀ S ∈ C, IsTopPart edge P D S := by
  constructor
  · intro hUnion S hSC
    refine
      ⟨hSeparated.1.1 S hSC, ?_, ?_⟩
    · intro x hxS
      apply hUnion.2.1
      exact
        Finset.mem_biUnion.mpr
          ⟨S, hSC, hxS⟩
    · intro u hu v hv huv
      have huD := (Finset.mem_sdiff.mp hu).1
      by_cases huUnion :
          u ∈ supportFamilyUnion C
      · obtain ⟨T, hTC, huT⟩ :=
          Finset.mem_biUnion.mp huUnion
        have hTS : T ≠ S := by
          intro hTS
          subst T
          exact (Finset.mem_sdiff.mp hu).2 huT
        exact
          hSeparated.2 T hTC S hSC hTS
            u huT v hv huv
      · exact
          hUnion.2.2 u
            (Finset.mem_sdiff.mpr
              ⟨huD, huUnion⟩)
            v
            (Finset.mem_biUnion.mpr
              ⟨S, hSC, hv⟩)
            huv
  · intro hComponents
    exact
      isTopPart_supportFamilyUnion hC hComponents

/-- A path in the union of a separated family which starts in one
component cannot leave that component. -/
theorem mem_of_reachInside_supportFamilyUnion_of_mem
    {edge : Vertex → Vertex → Prop}
    {C : Finset (Finset Vertex)}
    (hSeparated :
      IsSeparatedSupportFamily edge C)
    {S : Finset Vertex} (hSC : S ∈ C)
    {x y : Vertex} (hxS : x ∈ S)
    (hxy :
      ReachInside edge
        (supportFamilyUnion C) x y) :
    y ∈ S := by
  induction hxy with
  | refl =>
      exact hxS
  | @tail y z hxy hyz ih =>
      obtain ⟨T, hTC, hzT⟩ :=
        Finset.mem_biUnion.mp hyz.2.1
      by_cases hST : S = T
      · simpa [hST] using hzT
      · exact
          (hSeparated.2 S hSC T hTC hST
            y ih z hzT hyz.2.2).elim

/-- A finite vertex set has at most one decomposition into separated,
strongly connected, nonempty supports. -/
theorem eq_of_supportFamilyUnion_eq_of_separated_of_stronglyConnected
    {edge : Vertex → Vertex → Prop}
    {C T : Finset (Finset Vertex)}
    (hCSeparated :
      IsSeparatedSupportFamily edge C)
    (hTSeparated :
      IsSeparatedSupportFamily edge T)
    (hCStrong :
      ∀ S ∈ C,
        IsStronglyConnectedInside edge S)
    (hTStrong :
      ∀ S ∈ T,
        IsStronglyConnectedInside edge S)
    (hUnion :
      supportFamilyUnion C =
        supportFamilyUnion T) :
    C = T := by
  apply Finset.Subset.antisymm
  · intro S hSC
    obtain ⟨x, hxS⟩ :=
      hCSeparated.1.1 S hSC
    have hxUnionC :
        x ∈ supportFamilyUnion C :=
      Finset.mem_biUnion.mpr
        ⟨S, hSC, hxS⟩
    have hxUnionT :
        x ∈ supportFamilyUnion T := by
      rw [← hUnion]
      exact hxUnionC
    obtain ⟨U, hUT, hxU⟩ :=
      Finset.mem_biUnion.mp hxUnionT
    have hSU : S ⊆ U := by
      intro y hyS
      have hxyS :=
        hCStrong S hSC x hxS y hyS
      have hxyT :
          ReachInside edge
            (supportFamilyUnion T) x y := by
        apply reachInside_mono
        · intro z hzS
          rw [← hUnion]
          exact
            Finset.mem_biUnion.mpr
              ⟨S, hSC, hzS⟩
        · exact hxyS
      exact
        mem_of_reachInside_supportFamilyUnion_of_mem
          hTSeparated hUT hxU hxyT
    have hUS : U ⊆ S := by
      intro y hyU
      have hxyU :=
        hTStrong U hUT x hxU y hyU
      have hxyC :
          ReachInside edge
            (supportFamilyUnion C) x y := by
        apply reachInside_mono
        · intro z hzU
          rw [hUnion]
          exact
            Finset.mem_biUnion.mpr
              ⟨U, hUT, hzU⟩
        · exact hxyU
      exact
        mem_of_reachInside_supportFamilyUnion_of_mem
          hCSeparated hSC hxS hxyC
    have hSUeq : S = U :=
      Finset.Subset.antisymm hSU hUS
    simpa [hSUeq] using hUT
  · intro U hUT
    obtain ⟨x, hxU⟩ :=
      hTSeparated.1.1 U hUT
    have hxUnionT :
        x ∈ supportFamilyUnion T :=
      Finset.mem_biUnion.mpr
        ⟨U, hUT, hxU⟩
    have hxUnionC :
        x ∈ supportFamilyUnion C := by
      rw [hUnion]
      exact hxUnionT
    obtain ⟨S, hSC, hxS⟩ :=
      Finset.mem_biUnion.mp hxUnionC
    have hUS : U ⊆ S := by
      intro y hyU
      have hxyU :=
        hTStrong U hUT x hxU y hyU
      have hxyC :
          ReachInside edge
            (supportFamilyUnion C) x y := by
        apply reachInside_mono
        · intro z hzU
          rw [hUnion]
          exact
            Finset.mem_biUnion.mpr
              ⟨U, hUT, hzU⟩
        · exact hxyU
      exact
        mem_of_reachInside_supportFamilyUnion_of_mem
          hCSeparated hSC hxS hxyC
    have hSU : S ⊆ U := by
      intro y hyS
      have hxyS :=
        hCStrong S hSC x hxS y hyS
      have hxyT :
          ReachInside edge
            (supportFamilyUnion T) x y := by
        apply reachInside_mono
        · intro z hzS
          rw [← hUnion]
          exact
            Finset.mem_biUnion.mpr
              ⟨S, hSC, hzS⟩
        · exact hxyS
      exact
        mem_of_reachInside_supportFamilyUnion_of_mem
          hTSeparated hUT hxU hxyT
    have hSUeq : S = U :=
      Finset.Subset.antisymm hSU hUS
    simpa [← hSUeq] using hSC

/-- Nonempty subfamilies of `C`. -/
abbrev NonemptySubfamily
    (C : Finset (Finset Vertex)) :=
  {T : Finset (Finset Vertex) //
    T ∈ C.powerset.filter Finset.Nonempty}

/-- The union map on nonempty subfamilies. -/
def nonemptySubfamilyUnion
    (C : Finset (Finset Vertex))
    (T : NonemptySubfamily C) :
    Finset Vertex :=
  supportFamilyUnion T.1

/-- For a pairwise-disjoint nonempty support family, a subfamily is
determined by its union. -/
theorem nonemptySubfamilyUnion_injective
    {C : Finset (Finset Vertex)}
    (hC : IsDisjointNonemptySupportFamily C) :
    Function.Injective (nonemptySubfamilyUnion C) := by
  classical
  intro A B hAB
  apply Subtype.ext
  apply Finset.Subset.antisymm
  · intro S hSA
    have hASub : A.1 ⊆ C :=
      Finset.mem_powerset.mp
        (Finset.mem_filter.mp A.2).1
    have hBSub : B.1 ⊆ C :=
      Finset.mem_powerset.mp
        (Finset.mem_filter.mp B.2).1
    have hSC : S ∈ C :=
      hASub hSA
    obtain ⟨x, hxS⟩ :=
      hC.1 S hSC
    have hxA :
        x ∈ nonemptySubfamilyUnion C A := by
      exact
        Finset.mem_biUnion.mpr
          ⟨S, hSA, hxS⟩
    have hxB :
        x ∈ nonemptySubfamilyUnion C B := by
      rw [← hAB]
      exact hxA
    obtain ⟨T, hTB, hxT⟩ :=
      Finset.mem_biUnion.mp hxB
    have hTC : T ∈ C :=
      hBSub hTB
    by_cases hST : S = T
    · simpa [hST] using hTB
    · exact
        ((Finset.disjoint_left.mp
          (hC.2 S hSC T hTC hST))
            hxS hxT).elim
  · intro S hSB
    have hASub : A.1 ⊆ C :=
      Finset.mem_powerset.mp
        (Finset.mem_filter.mp A.2).1
    have hBSub : B.1 ⊆ C :=
      Finset.mem_powerset.mp
        (Finset.mem_filter.mp B.2).1
    have hSC : S ∈ C :=
      hBSub hSB
    obtain ⟨x, hxS⟩ :=
      hC.1 S hSC
    have hxB :
        x ∈ nonemptySubfamilyUnion C B := by
      exact
        Finset.mem_biUnion.mpr
          ⟨S, hSB, hxS⟩
    have hxA :
        x ∈ nonemptySubfamilyUnion C A := by
      rw [hAB]
      exact hxB
    obtain ⟨T, hTA, hxT⟩ :=
      Finset.mem_biUnion.mp hxA
    have hTC : T ∈ C :=
      hASub hTA
    by_cases hST : S = T
    · simpa [hST] using hTA
    · exact
        ((Finset.disjoint_left.mp
          (hC.2 S hSC T hTC hST))
            hxS hxT).elim

/-- Nonempty subfamilies are equivalent to their distinct support
unions. -/
noncomputable def nonemptySubfamilyUnionEquiv
    {C : Finset (Finset Vertex)}
    (hC : IsDisjointNonemptySupportFamily C) :
    NonemptySubfamily C ≃
      Set.range (nonemptySubfamilyUnion C) :=
  Equiv.ofInjective
    (nonemptySubfamilyUnion C)
    (nonemptySubfamilyUnion_injective hC)

/-- The number of components in a union, recovered from its unique
nonempty subfamily. -/
noncomputable def supportUnionComponentCount
    {C : Finset (Finset Vertex)}
    (hC : IsDisjointNonemptySupportFamily C)
    (W : Set.range (nonemptySubfamilyUnion C)) :
    ℕ :=
  ((nonemptySubfamilyUnionEquiv hC).symm W).1.card

/-- Grouping an alternating component sum by the support union preserves
the sign exponent: each union has one unique component subfamily. -/
theorem alternating_component_sum_group_by_union
    {C : Finset (Finset Vertex)}
    (hC : IsDisjointNonemptySupportFamily C)
    (weight : Finset Vertex → ℤ) :
    (∑ T : NonemptySubfamily C,
        (-1 : ℤ) ^ (T.1.card + 1) *
          weight (supportFamilyUnion T.1)) =
      ∑ W : Set.range (nonemptySubfamilyUnion C),
        (-1 : ℤ) ^
            (supportUnionComponentCount hC W + 1) *
          weight W.1 := by
  classical
  apply
    Fintype.sum_equiv
      (nonemptySubfamilyUnionEquiv hC)
  intro T
  unfold supportUnionComponentCount
  rw [(nonemptySubfamilyUnionEquiv hC).symm_apply_apply]
  rfl

/-- The inclusion--exclusion signs of all nonempty subfamilies of a
nonempty finite family sum to one. -/
theorem alternating_nonempty_subfamilies_sum
    {C : Finset (Finset Vertex)}
    (hCnonempty : C.Nonempty) :
    (∑ T ∈ C.powerset.filter Finset.Nonempty,
      (-1 : ℤ) ^ (T.card + 1)) = 1 := by
  classical
  have hfilter :
      C.powerset.filter Finset.Nonempty =
        C.powerset.erase ∅ := by
    ext T
    simp [Finset.nonempty_iff_ne_empty,
      and_comm]
  rw [hfilter]
  have hall :=
    Finset.sum_powerset_neg_one_pow_card_of_nonempty
      hCnonempty
  have herase :=
    Finset.sum_erase_add C.powerset
      (fun T : Finset (Finset Vertex) ↦
        (-1 : ℤ) ^ T.card)
      (Finset.empty_mem_powerset C)
  have hbase :
      (∑ T ∈ C.powerset.erase ∅,
        (-1 : ℤ) ^ T.card) = -1 := by
    calc
      (∑ T ∈ C.powerset.erase ∅,
          (-1 : ℤ) ^ T.card) =
          (∑ T ∈ C.powerset,
            (-1 : ℤ) ^ T.card) - 1 := by
        apply eq_sub_of_add_eq
        convert herase using 1
        all_goals norm_num
      _ = 0 - 1 := by rw [hall]
      _ = -1 := by norm_num
  calc
    (∑ T ∈ C.powerset.erase ∅,
        (-1 : ℤ) ^ (T.card + 1)) =
        - ∑ T ∈ C.powerset.erase ∅,
          (-1 : ℤ) ^ T.card := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro T hT
      rw [pow_succ]
      ring
    _ = 1 := by rw [hbase]; norm_num

/-- After grouping by union, the aggregate Möbius coefficient is still
one. -/
theorem alternating_support_unions_sum
    {C : Finset (Finset Vertex)}
    (hC : IsDisjointNonemptySupportFamily C)
    (hCnonempty : C.Nonempty) :
    (∑ W : Set.range (nonemptySubfamilyUnion C),
      (-1 : ℤ) ^
        (supportUnionComponentCount hC W + 1)) = 1 := by
  have hgroup :=
    alternating_component_sum_group_by_union
      hC (fun _ ↦ (1 : ℤ))
  simp only [mul_one] at hgroup
  rw [← hgroup]
  change
    (∑ T ∈
        (C.powerset.filter
          Finset.Nonempty).attach,
      (-1 : ℤ) ^ (T.1.card + 1)) = 1
  calc
    (∑ T ∈
        (C.powerset.filter
          Finset.Nonempty).attach,
      (-1 : ℤ) ^ (T.1.card + 1)) =
        ∑ T ∈ C.powerset.filter
          Finset.Nonempty,
          (-1 : ℤ) ^ (T.card + 1) := by
      exact
        Finset.sum_attach
          (C.powerset.filter
            Finset.Nonempty)
          (fun T ↦
            (-1 : ℤ) ^ (T.card + 1))
    _ = 1 :=
      alternating_nonempty_subfamilies_sum
        (Vertex := Vertex) hCnonempty

/-- A path cannot enter a vertex set across which there is no incoming
edge. -/
theorem not_mem_of_reachInside_of_no_entry
    {edge : Vertex → Vertex → Prop}
    {D S : Finset Vertex}
    (hnoEntry :
      ∀ u ∈ D \ S, ∀ v ∈ S, ¬ edge u v)
    {x y : Vertex} (hx : x ∉ S)
    (hxy : ReachInside edge D x y) :
    y ∉ S := by
  induction hxy with
  | refl =>
      exact hx
  | @tail y z hxy hyz ih =>
      intro hzS
      exact
        hnoEntry y
          (Finset.mem_sdiff.mpr ⟨hyz.1, ih⟩)
          z hzS hyz.2.2

/-- A strongly connected top part is inclusion-minimal. -/
theorem isMinimalTopPart_of_isTopPart_of_isStronglyConnectedInside
    {edge : Vertex → Vertex → Prop}
    {P D S : Finset Vertex}
    (hTop : IsTopPart edge P D S)
    (hStrong : IsStronglyConnectedInside edge S) :
    IsMinimalTopPart edge P D S := by
  refine ⟨hTop, ?_⟩
  intro T hT hTS x hxS
  by_contra hxT
  obtain ⟨y, hyT⟩ := hT.1
  have hyS : y ∈ S := hTS hyT
  have hxyS :
      ReachInside edge S x y :=
    hStrong x hxS y hyS
  have hxyD :
      ReachInside edge D x y := by
    have hrel :
        InsideEdge edge S ≤ InsideEdge edge D := by
      intro u v huv
      exact
        ⟨(Finset.mem_sdiff.mp
            (hTop.2.1 huv.1)).1,
          (Finset.mem_sdiff.mp
            (hTop.2.1 huv.2.1)).1,
          huv.2.2⟩
    exact
      Relation.ReflTransGen.mono hrel x y hxyS
  exact
    (not_mem_of_reachInside_of_no_entry
      hT.2.2 hxT hxyD) hyT

/-- Minimal top parts are exactly the strongly connected top parts. -/
theorem isMinimalTopPart_iff_isTopPart_and_isStronglyConnectedInside
    {edge : Vertex → Vertex → Prop}
    {P D S : Finset Vertex} :
    IsMinimalTopPart edge P D S ↔
      IsTopPart edge P D S ∧
        IsStronglyConnectedInside edge S := by
  constructor
  · intro hS
    exact
      ⟨hS.1,
        isStronglyConnectedInside_of_isMinimalTopPart hS⟩
  · rintro ⟨hTop, hStrong⟩
    exact
      isMinimalTopPart_of_isTopPart_of_isStronglyConnectedInside
        hTop hStrong

/-- A selected vertex set is not projectively rooted exactly when it has
a top part. -/
theorem not_isProjectivelyRooted_iff_exists_isTopPart
    (edge : Vertex → Vertex → Prop)
    (P D : Finset Vertex) :
    ¬ IsProjectivelyRooted edge P D ↔
      ∃ S : Finset Vertex, IsTopPart edge P D S := by
  constructor
  · intro hnotRooted
    rw [IsProjectivelyRooted] at hnotRooted
    push Not at hnotRooted
    obtain ⟨x, hxD, hxUnreached⟩ := hnotRooted
    let S := unreachableVertices edge P D
    refine ⟨S, ?_, ?_, ?_⟩
    · exact
        ⟨x, (mem_unreachableVertices (edge := edge)
          (P := P) (D := D)).2 ⟨hxD, hxUnreached⟩⟩
    · intro y hyS
      have hy :=
        (mem_unreachableVertices (edge := edge)
          (P := P) (D := D)).1 hyS
      apply Finset.mem_sdiff.mpr
      refine ⟨hy.1, ?_⟩
      intro hyP
      apply hy.2
      exact
        ⟨y, hyP, hy.1,
          Relation.ReflTransGen.refl⟩
    · intro u hu v hv huv
      have huD : u ∈ D :=
        (Finset.mem_sdiff.mp hu).1
      have huReached :
          ReachedFromBoundary edge P D u := by
        by_contra huUnreached
        have huS : u ∈ S :=
          (mem_unreachableVertices (edge := edge)
            (P := P) (D := D)).2
              ⟨huD, huUnreached⟩
        exact (Finset.mem_sdiff.mp hu).2 huS
      obtain ⟨p, hpP, hpD, hpu⟩ := huReached
      have hvData :=
        (mem_unreachableVertices (edge := edge)
          (P := P) (D := D)).1 hv
      apply hvData.2
      exact
        ⟨p, hpP, hpD,
          hpu.tail ⟨huD, hvData.1, huv⟩⟩
  · rintro ⟨S, hSnonempty, hSsub, hnoEntry⟩
    intro hrooted
    obtain ⟨x, hxS⟩ := hSnonempty
    have hxD : x ∈ D :=
      (Finset.mem_sdiff.mp (hSsub hxS)).1
    obtain ⟨p, hpP, hpD, hpx⟩ :=
      hrooted x hxD
    have hpS : p ∉ S := by
      intro hpS
      exact
        (Finset.mem_sdiff.mp (hSsub hpS)).2 hpP
    exact
      (not_mem_of_reachInside_of_no_entry
        hnoEntry hpS hpx) hxS

/-- A selected set is nonrooted exactly when it has a minimal top
part. -/
theorem not_isProjectivelyRooted_iff_exists_isMinimalTopPart
    (edge : Vertex → Vertex → Prop)
    (P D : Finset Vertex) :
    ¬ IsProjectivelyRooted edge P D ↔
      ∃ S : Finset Vertex,
        IsMinimalTopPart edge P D S := by
  constructor
  · intro hD
    obtain ⟨S, hS⟩ :=
      (not_isProjectivelyRooted_iff_exists_isTopPart
        edge P D).1 hD
    obtain ⟨T, hT, hTS⟩ :=
      exists_isMinimalTopPart_subset hS
    exact ⟨T, hT⟩
  · rintro ⟨S, hS⟩
    exact
      (not_isProjectivelyRooted_iff_exists_isTopPart
        edge P D).2 ⟨S, hS.1⟩

/-- The canonical family is nonempty exactly for a nonrooted selected
set. -/
theorem minimalTopParts_nonempty_iff_not_isProjectivelyRooted
    (edge : Vertex → Vertex → Prop)
    (P D : Finset Vertex) :
    (minimalTopParts edge P D).Nonempty ↔
      ¬ IsProjectivelyRooted edge P D := by
  constructor
  · rintro ⟨S, hS⟩
    apply
      (not_isProjectivelyRooted_iff_exists_isMinimalTopPart
        edge P D).2
    exact
      ⟨S,
        (mem_minimalTopParts
          (edge := edge) (P := P) (D := D)).1 hS⟩
  · intro hD
    obtain ⟨S, hS⟩ :=
      (not_isProjectivelyRooted_iff_exists_isMinimalTopPart
        edge P D).1 hD
    exact
      ⟨S,
        (mem_minimalTopParts
          (edge := edge) (P := P) (D := D)).2 hS⟩

/-- Every top part contains a member of the canonical minimal family. -/
theorem exists_mem_minimalTopParts_subset
    {edge : Vertex → Vertex → Prop}
    {P D S : Finset Vertex}
    (hS : IsTopPart edge P D S) :
    ∃ T ∈ minimalTopParts edge P D, T ⊆ S := by
  obtain ⟨T, hTminimal, hTS⟩ :=
    exists_isMinimalTopPart_subset hS
  exact
    ⟨T,
      (mem_minimalTopParts
        (edge := edge) (P := P) (D := D)).2
        hTminimal,
      hTS⟩

/-- Injective corootedness is projective rootedness for the reversed
edge relation. -/
def IsInjectivelyCorooted
    (edge : Vertex → Vertex → Prop)
    (I D : Finset Vertex) : Prop :=
  IsProjectivelyRooted (fun x y ↦ edge y x) I D

/-- The dual obstruction: a nonempty set of noninjective vertices with
no edge leaving it for the rest of `D`. -/
def IsBottomPart
    (edge : Vertex → Vertex → Prop)
    (I D S : Finset Vertex) : Prop :=
  S.Nonempty ∧
    S ⊆ D \ I ∧
    ∀ u ∈ S, ∀ v ∈ D \ S, ¬ edge u v

/-- A selected vertex set is not injectively corooted exactly when it has
a bottom part. -/
theorem not_isInjectivelyCorooted_iff_exists_isBottomPart
    (edge : Vertex → Vertex → Prop)
    (I D : Finset Vertex) :
    ¬ IsInjectivelyCorooted edge I D ↔
      ∃ S : Finset Vertex, IsBottomPart edge I D S := by
  rw [IsInjectivelyCorooted,
    not_isProjectivelyRooted_iff_exists_isTopPart]
  constructor
  · rintro ⟨S, hSnonempty, hSsub, hnoEntry⟩
    refine ⟨S, hSnonempty, hSsub, ?_⟩
    intro u hu v hv
    exact hnoEntry v hv u hu
  · rintro ⟨S, hSnonempty, hSsub, hnoExit⟩
    refine ⟨S, hSnonempty, hSsub, ?_⟩
    intro u hu v hv
    exact hnoExit v hv u hu

section InclusionExclusion

variable [Fintype Vertex]

/-- All vertex sets of cardinality `j`. -/
def setsOfCard (j : ℕ) : Finset (Finset Vertex) :=
  Finset.univ.powersetCard j

omit [DecidableEq Vertex] in
@[simp]
theorem mem_setsOfCard {j : ℕ} {D : Finset Vertex} :
    D ∈ setsOfCard (Vertex := Vertex) j ↔ D.card = j := by
  simp [setsOfCard]

/-- Projectively rooted vertex sets of cardinality `j`. -/
def projectivelyRootedSets
    (edge : Vertex → Vertex → Prop)
    (P : Finset Vertex) (j : ℕ) :
    Finset (Finset Vertex) :=
  by
    classical
    exact
      (setsOfCard (Vertex := Vertex) j).filter fun D ↦
        IsProjectivelyRooted edge P D

omit [DecidableEq Vertex] in
@[simp]
theorem mem_projectivelyRootedSets
    {edge : Vertex → Vertex → Prop}
    {P : Finset Vertex} {j : ℕ} {D : Finset Vertex} :
    D ∈ projectivelyRootedSets edge P j ↔
      D.card = j ∧ IsProjectivelyRooted edge P D := by
  classical
  simp [projectivelyRootedSets]

/-- Non-projectively-rooted vertex sets of cardinality `j`. -/
def nonProjectivelyRootedSets
    (edge : Vertex → Vertex → Prop)
    (P : Finset Vertex) (j : ℕ) :
    Finset (Finset Vertex) :=
  by
    classical
    exact
      (setsOfCard (Vertex := Vertex) j).filter fun D ↦
        ¬ IsProjectivelyRooted edge P D

omit [DecidableEq Vertex] in
@[simp]
theorem mem_nonProjectivelyRootedSets
    {edge : Vertex → Vertex → Prop}
    {P : Finset Vertex} {j : ℕ} {D : Finset Vertex} :
    D ∈ nonProjectivelyRootedSets edge P j ↔
      D.card = j ∧ ¬ IsProjectivelyRooted edge P D := by
  classical
  simp [nonProjectivelyRootedSets]

/-- All possible top-part supports: nonempty vertex sets disjoint from
the projective boundary.  Supports which cannot actually occur simply
index an empty event below. -/
def topPartCandidates (P : Finset Vertex) :
    Finset (Finset Vertex) :=
  by
    classical
    exact
      (Finset.univ : Finset Vertex).powerset.filter fun S ↦
        S.Nonempty ∧ ∀ x ∈ S, x ∉ P

@[simp]
theorem mem_topPartCandidates
    {P S : Finset Vertex} :
    S ∈ topPartCandidates P ↔
      S.Nonempty ∧ ∀ x ∈ S, x ∉ P := by
  classical
  simp [topPartCandidates]

/-- Candidate supports which are strongly connected.  Whenever such a
support occurs as a top part of `D`, it is automatically a minimal top
part of `D`. -/
def minimalTopPartCandidates
    (edge : Vertex → Vertex → Prop)
    (P : Finset Vertex) :
    Finset (Finset Vertex) :=
  by
    classical
    exact
      (topPartCandidates P).filter fun S ↦
        IsStronglyConnectedInside edge S

@[simp]
theorem mem_minimalTopPartCandidates
    {edge : Vertex → Vertex → Prop}
    {P S : Finset Vertex} :
    S ∈ minimalTopPartCandidates edge P ↔
      S ∈ topPartCandidates P ∧
        IsStronglyConnectedInside edge S := by
  classical
  simp [minimalTopPartCandidates]

/-- The union of a nonempty family of candidate supports is again a
candidate support. -/
theorem supportFamilyUnion_mem_topPartCandidates
    {P : Finset Vertex}
    {C : Finset (Finset Vertex)}
    (hC : C.Nonempty)
    (hCandidates :
      ∀ S ∈ C, S ∈ topPartCandidates P) :
    supportFamilyUnion C ∈ topPartCandidates P := by
  apply mem_topPartCandidates.mpr
  obtain ⟨S, hSC⟩ := hC
  obtain ⟨x, hxS⟩ :=
    (mem_topPartCandidates.mp
      (hCandidates S hSC)).1
  constructor
  · exact
      ⟨x,
        Finset.mem_biUnion.mpr
          ⟨S, hSC, hxS⟩⟩
  · intro y hyUnion
    obtain ⟨T, hTC, hyT⟩ :=
      Finset.mem_biUnion.mp hyUnion
    exact
      (mem_topPartCandidates.mp
        (hCandidates T hTC)).2 y hyT

/-- In particular, a nonempty union of strongly connected candidate
supports remains an ordinary candidate support. -/
theorem supportFamilyUnion_mem_topPartCandidates_of_minimalCandidates
    {edge : Vertex → Vertex → Prop}
    {P : Finset Vertex}
    {C : Finset (Finset Vertex)}
    (hC : C.Nonempty)
    (hCandidates :
      ∀ S ∈ C,
        S ∈ minimalTopPartCandidates edge P) :
    supportFamilyUnion C ∈ topPartCandidates P := by
  apply supportFamilyUnion_mem_topPartCandidates hC
  intro S hSC
  exact
    (mem_minimalTopPartCandidates.mp
      (hCandidates S hSC)).1

/-- Nonempty separated families of strongly connected candidate
supports.  These are precisely the raw families whose event
intersection can be nonempty. -/
def separatedMinimalTopPartFamilies
    (edge : Vertex → Vertex → Prop)
    (P : Finset Vertex) :
    Finset (Finset (Finset Vertex)) :=
  by
    classical
    exact
      (minimalTopPartCandidates edge P).powerset.filter
        fun C ↦
          C.Nonempty ∧
            IsSeparatedSupportFamily edge C

@[simp]
theorem mem_separatedMinimalTopPartFamilies
    {edge : Vertex → Vertex → Prop}
    {P : Finset Vertex}
    {C : Finset (Finset Vertex)} :
    C ∈ separatedMinimalTopPartFamilies edge P ↔
      C ⊆ minimalTopPartCandidates edge P ∧
        C.Nonempty ∧
          IsSeparatedSupportFamily edge C := by
  classical
  simp [separatedMinimalTopPartFamilies]

/-- The finite type of nonempty separated families of minimal
candidate supports. -/
abbrev SeparatedMinimalTopPartFamily
    (edge : Vertex → Vertex → Prop)
    (P : Finset Vertex) :=
  {C : Finset (Finset Vertex) //
    C ∈ separatedMinimalTopPartFamilies edge P}

/-- The support union of a separated minimal-candidate family. -/
def separatedMinimalTopPartFamilyUnion
    (edge : Vertex → Vertex → Prop)
    (P : Finset Vertex)
    (C : SeparatedMinimalTopPartFamily edge P) :
    Finset Vertex :=
  supportFamilyUnion C.1

/-- The union represented by a separated minimal-candidate family is
an ordinary top-part candidate. -/
theorem separatedMinimalTopPartFamilyUnion_mem_topPartCandidates
    (edge : Vertex → Vertex → Prop)
    (P : Finset Vertex)
    (C : SeparatedMinimalTopPartFamily edge P) :
    separatedMinimalTopPartFamilyUnion edge P C ∈
      topPartCandidates P := by
  have hC :=
    mem_separatedMinimalTopPartFamilies.mp C.2
  apply
    supportFamilyUnion_mem_topPartCandidates_of_minimalCandidates
      hC.2.1
  intro S hSC
  exact hC.1 hSC

/-- A separated family of strongly connected candidate supports is
globally determined by its union, not merely among subfamilies of one
fixed component family. -/
theorem separatedMinimalTopPartFamilyUnion_injective
    (edge : Vertex → Vertex → Prop)
    (P : Finset Vertex) :
    Function.Injective
      (separatedMinimalTopPartFamilyUnion edge P) := by
  intro C T hUnion
  apply Subtype.ext
  have hC :=
    (mem_separatedMinimalTopPartFamilies.mp C.2)
  have hT :=
    (mem_separatedMinimalTopPartFamilies.mp T.2)
  apply
    eq_of_supportFamilyUnion_eq_of_separated_of_stronglyConnected
      hC.2.2 hT.2.2
  · intro S hSC
    exact
      (mem_minimalTopPartCandidates.mp
        (hC.1 hSC)).2
  · intro S hST
    exact
      (mem_minimalTopPartCandidates.mp
        (hT.1 hST)).2
  · exact hUnion

/-- Separated component families are equivalent to their distinct
support unions. -/
noncomputable def separatedMinimalTopPartFamilyUnionEquiv
    (edge : Vertex → Vertex → Prop)
    (P : Finset Vertex) :
    SeparatedMinimalTopPartFamily edge P ≃
      Set.range
        (separatedMinimalTopPartFamilyUnion edge P) :=
  Equiv.ofInjective
    (separatedMinimalTopPartFamilyUnion edge P)
    (separatedMinimalTopPartFamilyUnion_injective
      edge P)

/-- The canonical number of strongly connected separated components
in a support union. -/
noncomputable def separatedSupportUnionComponentCount
    (edge : Vertex → Vertex → Prop)
    (P : Finset Vertex)
    (W :
      Set.range
        (separatedMinimalTopPartFamilyUnion edge P)) :
    ℕ :=
  ((separatedMinimalTopPartFamilyUnionEquiv
    edge P).symm W).1.card

/-- The event that a fixed support `S` is a top part of a selected
`j`-set `D`. -/
def topPartEvent
    (edge : Vertex → Vertex → Prop)
    (P : Finset Vertex) (j : ℕ) (S : Finset Vertex) :
    Finset (Finset Vertex) :=
  by
    classical
    exact
      (setsOfCard (Vertex := Vertex) j).filter fun D ↦
        IsTopPart edge P D S

@[simp]
theorem mem_topPartEvent
    {edge : Vertex → Vertex → Prop}
    {P S D : Finset Vertex} {j : ℕ} :
    D ∈ topPartEvent edge P j S ↔
      D.card = j ∧ IsTopPart edge P D S := by
  classical
  simp [topPartEvent]

/-- On a strongly connected candidate support, event membership says
precisely that the support is a minimal top part. -/
theorem mem_topPartEvent_iff_card_and_isMinimalTopPart
    {edge : Vertex → Vertex → Prop}
    {P S D : Finset Vertex} {j : ℕ}
    (hS :
      S ∈ minimalTopPartCandidates edge P) :
    D ∈ topPartEvent edge P j S ↔
      D.card = j ∧
        IsMinimalTopPart edge P D S := by
  rw [mem_topPartEvent]
  constructor
  · rintro ⟨hDcard, hStop⟩
    refine ⟨hDcard, ?_⟩
    apply
      isMinimalTopPart_of_isTopPart_of_isStronglyConnectedInside
        hStop
    exact
      (mem_minimalTopPartCandidates.mp hS).2
  · rintro ⟨hDcard, hSminimal⟩
    exact ⟨hDcard, hSminimal.1⟩

/-- For a separated nonempty support family, the intersection of its
top-part events is exactly the event indexed by the support union. -/
theorem inf'_topPartEvent_eq_topPartEvent_supportFamilyUnion
    (edge : Vertex → Vertex → Prop)
    (P : Finset Vertex) (j : ℕ)
    {C : Finset (Finset Vertex)}
    (hC : C.Nonempty)
    (hSeparated :
      IsSeparatedSupportFamily edge C) :
    C.inf' hC (topPartEvent edge P j) =
      topPartEvent edge P j
        (supportFamilyUnion C) := by
  ext D
  simp only [Finset.mem_inf',
    mem_topPartEvent]
  constructor
  · intro hEvents
    have hUnion :
        IsTopPart edge P D
          (supportFamilyUnion C) :=
      (isTopPart_supportFamilyUnion_iff
        hC hSeparated).2
        (fun T hTC ↦ (hEvents T hTC).2)
    obtain ⟨S, hSC⟩ := hC
    refine
      ⟨(hEvents S hSC).1, hUnion⟩
  · rintro ⟨hDcard, hUnion⟩ S hSC
    exact
      ⟨hDcard,
        (isTopPart_supportFamilyUnion_iff
          hC hSeparated).1 hUnion S hSC⟩

/-- If a selected set lies in all events of a family of strongly
connected candidates, those candidates are its minimal top parts and
therefore form a separated family. -/
theorem isSeparatedSupportFamily_of_mem_inf'_minimalTopPartEvents
    {edge : Vertex → Vertex → Prop}
    {P : Finset Vertex} {j : ℕ}
    {C : Finset (Finset Vertex)}
    (hC : C.Nonempty)
    (hCandidates :
      ∀ S ∈ C,
        S ∈ minimalTopPartCandidates edge P)
    {D : Finset Vertex}
    (hD :
      D ∈ C.inf' hC
        (topPartEvent edge P j)) :
    IsSeparatedSupportFamily edge C := by
  apply isSeparatedSupportFamily_of_minimalTopParts
  intro S hSC
  have hSEvent :=
    (Finset.mem_inf' hC).1 hD S hSC
  exact
    (mem_topPartEvent_iff_card_and_isMinimalTopPart
      (D := D) (j := j)
      (hCandidates S hSC)).1 hSEvent |>.2

/-- A nonseparated family of strongly connected candidates has empty
event intersection. -/
theorem inf'_minimalTopPartEvents_eq_empty_of_not_separated
    {edge : Vertex → Vertex → Prop}
    {P : Finset Vertex} {j : ℕ}
    {C : Finset (Finset Vertex)}
    (hC : C.Nonempty)
    (hCandidates :
      ∀ S ∈ C,
        S ∈ minimalTopPartCandidates edge P)
    (hNotSeparated :
      ¬ IsSeparatedSupportFamily edge C) :
    C.inf' hC (topPartEvent edge P j) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro D hD
  exact
    hNotSeparated
      (isSeparatedSupportFamily_of_mem_inf'_minimalTopPartEvents
        hC hCandidates hD)

/-- Immediate predecessors of a vertex support. -/
def immediatePredecessors
    (edge : Vertex → Vertex → Prop)
    (S : Finset Vertex) : Finset Vertex :=
  by
    classical
    exact
      Finset.univ.filter fun x ↦
        ∃ y ∈ S, edge x y

omit [DecidableEq Vertex] in
@[simp]
theorem mem_immediatePredecessors
    {edge : Vertex → Vertex → Prop}
    {S : Finset Vertex} {x : Vertex} :
    x ∈ immediatePredecessors edge S ↔
      ∃ y ∈ S, edge x y := by
  classical
  simp [immediatePredecessors]

/-- The forced region attached to a top-part support: the support and
all of its immediate predecessors. -/
def topPartForcedRegion
    (edge : Vertex → Vertex → Prop)
    (S : Finset Vertex) : Finset Vertex :=
  S ∪ immediatePredecessors edge S

/-- Vertices free to be added once a top-part support has been fixed. -/
def topPartFreeVertices
    (edge : Vertex → Vertex → Prop)
    (S : Finset Vertex) : Finset Vertex :=
  Finset.univ \ topPartForcedRegion edge S

/-- The complete ambient set from which a set having `S` as a top part
may be selected: `S` itself together with the free vertices. -/
def topPartAllowedVertices
    (edge : Vertex → Vertex → Prop)
    (S : Finset Vertex) : Finset Vertex :=
  S ∪ topPartFreeVertices edge S

theorem subset_topPartAllowedVertices
    (edge : Vertex → Vertex → Prop)
    (S : Finset Vertex) :
    S ⊆ topPartAllowedVertices edge S :=
  Finset.subset_union_left

theorem disjoint_topPartFreeVertices
    (edge : Vertex → Vertex → Prop)
    (S : Finset Vertex) :
    Disjoint S (topPartFreeVertices edge S) := by
  classical
  rw [Finset.disjoint_left]
  intro x hxS hxFree
  exact
    (Finset.mem_sdiff.mp hxFree).2
      (Finset.mem_union_left
        (immediatePredecessors edge S) hxS)

/-- Having a fixed candidate `S` as a top part means choosing a
cardinality-`j` superset of `S` from `S` together with the vertices
outside `S ∪ N⁻(S)`. -/
theorem topPartEvent_eq_filter_powersetCard_allowed
    (edge : Vertex → Vertex → Prop)
    (P : Finset Vertex) (j : ℕ)
    {S : Finset Vertex}
    (hScandidate : S ∈ topPartCandidates P) :
    topPartEvent edge P j S =
      ((topPartAllowedVertices edge S).powersetCard j).filter
        (S ⊆ ·) := by
  classical
  have hSdata :=
    (mem_topPartCandidates
      (P := P) (S := S)).1 hScandidate
  ext D
  rw [mem_topPartEvent, Finset.mem_filter,
    Finset.mem_powersetCard]
  constructor
  · rintro ⟨hDcard, hStop⟩
    refine ⟨⟨?_, hDcard⟩, ?_⟩
    · intro x hxD
      by_cases hxS : x ∈ S
      · exact
          Finset.mem_union_left
            (topPartFreeVertices edge S) hxS
      · apply Finset.mem_union_right
        apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_univ x, ?_⟩
        intro hxForced
        rcases Finset.mem_union.mp hxForced with
          hxS' | hxPred
        · exact hxS hxS'
        · obtain ⟨y, hyS, hxy⟩ :=
            (mem_immediatePredecessors
              (edge := edge) (S := S)).1 hxPred
          exact
            hStop.2.2 x
              (Finset.mem_sdiff.mpr ⟨hxD, hxS⟩)
              y hyS hxy
    · intro x hxS
      exact (Finset.mem_sdiff.mp (hStop.2.1 hxS)).1
  · rintro ⟨⟨hDallowed, hDcard⟩, hSD⟩
    refine ⟨hDcard, hSdata.1, ?_, ?_⟩
    · intro x hxS
      apply Finset.mem_sdiff.mpr
      exact ⟨hSD hxS, hSdata.2 x hxS⟩
    · intro x hxDminus y hyS hxy
      have hxAllowed :=
        hDallowed (Finset.mem_sdiff.mp hxDminus).1
      rcases Finset.mem_union.mp hxAllowed with
        hxS | hxFree
      · exact (Finset.mem_sdiff.mp hxDminus).2 hxS
      · exact
          (Finset.mem_sdiff.mp hxFree).2
            (Finset.mem_union_right S
              ((mem_immediatePredecessors
                (edge := edge) (S := S)).2
                  ⟨y, hyS, hxy⟩))

/-- Exact binomial count of a fixed top-part event, in terms of the
vertices outside the forced region. -/
theorem topPartEvent_card_eq_choose_freeVertices
    (edge : Vertex → Vertex → Prop)
    (P : Finset Vertex) (j : ℕ)
    {S : Finset Vertex}
    (hScandidate : S ∈ topPartCandidates P)
    (hSj : S.card ≤ j) :
    (topPartEvent edge P j S).card =
      Nat.choose (topPartFreeVertices edge S).card
        (j - S.card) := by
  rw [topPartEvent_eq_filter_powersetCard_allowed
    edge P j hScandidate]
  rw [Finset.card_filter_powersetCard_subset
    S (topPartAllowedVertices edge S) j
      (subset_topPartAllowedVertices edge S) hSj]
  have hdisjoint :=
    disjoint_topPartFreeVertices edge S
  rw [topPartAllowedVertices,
    Finset.card_union_of_disjoint hdisjoint]
  rw [Nat.add_sub_cancel_left]

/-- The number of free vertices is the total number of vertices minus
the size of `S ∪ N⁻(S)`. -/
theorem topPartFreeVertices_card
    (edge : Vertex → Vertex → Prop)
    (S : Finset Vertex) :
    (topPartFreeVertices edge S).card =
      Fintype.card Vertex -
        (topPartForcedRegion edge S).card := by
  rw [topPartFreeVertices,
    Finset.card_sdiff_of_subset
      (Finset.subset_univ _),
    Finset.card_univ]

/-- Paper-form count of a fixed top-part event:
`choose (N - |S ∪ N⁻(S)|) (j - |S|)`. -/
theorem topPartEvent_card_eq_choose_forcedRegion
    (edge : Vertex → Vertex → Prop)
    (P : Finset Vertex) (j : ℕ)
    {S : Finset Vertex}
    (hScandidate : S ∈ topPartCandidates P)
    (hSj : S.card ≤ j) :
    (topPartEvent edge P j S).card =
      Nat.choose
        (Fintype.card Vertex -
          (topPartForcedRegion edge S).card)
        (j - S.card) := by
  rw [topPartEvent_card_eq_choose_freeVertices
      edge P j hScandidate hSj,
    topPartFreeVertices_card]

/-- A support larger than the prescribed selected-set cardinality has
an empty top-part event. -/
theorem topPartEvent_eq_empty_of_card_lt
    (edge : Vertex → Vertex → Prop)
    (P : Finset Vertex) (j : ℕ)
    {S : Finset Vertex}
    (hSj : j < S.card) :
    topPartEvent edge P j S = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro D hD
  have hEvent :=
    (mem_topPartEvent
      (edge := edge) (P := P)
      (S := S) (D := D) (j := j)).1 hD
  have hSD : S ⊆ D := by
    intro x hxS
    exact
      (Finset.mem_sdiff.mp
        (hEvent.2.2.1 hxS)).1
  have hCard := Finset.card_le_card hSD
  omega

/-- Uniform fixed-support count, including the case in which the
support is too large for a `j`-set. -/
theorem topPartEvent_card_eq_if_choose_forcedRegion
    (edge : Vertex → Vertex → Prop)
    (P : Finset Vertex) (j : ℕ)
    {S : Finset Vertex}
    (hScandidate : S ∈ topPartCandidates P) :
    (topPartEvent edge P j S).card =
      if S.card ≤ j then
        Nat.choose
          (Fintype.card Vertex -
            (topPartForcedRegion edge S).card)
          (j - S.card)
      else 0 := by
  by_cases hSj : S.card ≤ j
  · rw [if_pos hSj]
    exact
      topPartEvent_card_eq_choose_forcedRegion
        edge P j hScandidate hSj
  · rw [if_neg hSj,
      topPartEvent_eq_empty_of_card_lt
        edge P j (Nat.lt_of_not_ge hSj)]
    simp

/-- It is enough to cover nonrooted sets by the events of strongly
connected candidate supports: in every event these are exactly the
minimal top parts. -/
theorem biUnion_minimalTopPartEvents_eq_nonProjectivelyRootedSets
    (edge : Vertex → Vertex → Prop)
    (P : Finset Vertex) (j : ℕ) :
    (minimalTopPartCandidates edge P).biUnion
        (topPartEvent edge P j) =
      nonProjectivelyRootedSets edge P j := by
  classical
  ext D
  constructor
  · intro hD
    obtain ⟨S, hScandidate, hDevent⟩ :=
      Finset.mem_biUnion.mp hD
    have hEvent :=
      (mem_topPartEvent_iff_card_and_isMinimalTopPart
        (D := D) (j := j) hScandidate).1 hDevent
    exact
      (mem_nonProjectivelyRootedSets
        (edge := edge) (P := P) (j := j)).2
        ⟨hEvent.1,
          (not_isProjectivelyRooted_iff_exists_isMinimalTopPart
            edge P D).2 ⟨S, hEvent.2⟩⟩
  · intro hD
    have hNonrooted :=
      (mem_nonProjectivelyRootedSets
        (edge := edge) (P := P) (j := j)).1 hD
    obtain ⟨S, hSminimal⟩ :=
      (not_isProjectivelyRooted_iff_exists_isMinimalTopPart
        edge P D).1 hNonrooted.2
    apply Finset.mem_biUnion.mpr
    refine ⟨S, ?_, ?_⟩
    · apply mem_minimalTopPartCandidates.mpr
      refine ⟨?_, ?_⟩
      · apply mem_topPartCandidates.mpr
        refine ⟨hSminimal.1.1, ?_⟩
        intro x hxS hxP
        exact
          (Finset.mem_sdiff.mp
            (hSminimal.1.2.1 hxS)).2 hxP
      · exact
          isStronglyConnectedInside_of_isMinimalTopPart
            hSminimal
    · exact
        (mem_topPartEvent_iff_card_and_isMinimalTopPart
          (D := D) (j := j)
          (by
            apply mem_minimalTopPartCandidates.mpr
            refine ⟨?_, ?_⟩
            · apply mem_topPartCandidates.mpr
              refine ⟨hSminimal.1.1, ?_⟩
              intro x hxS hxP
              exact
                (Finset.mem_sdiff.mp
                  (hSminimal.1.2.1 hxS)).2 hxP
            · exact
                isStronglyConnectedInside_of_isMinimalTopPart
                  hSminimal)).2
          ⟨hNonrooted.1, hSminimal⟩

/-- The union of all top-part events is exactly the family of
non-projectively-rooted `j`-sets. -/
theorem biUnion_topPartEvents_eq_nonProjectivelyRootedSets
    (edge : Vertex → Vertex → Prop)
    (P : Finset Vertex) (j : ℕ) :
    (topPartCandidates P).biUnion
        (topPartEvent edge P j) =
      nonProjectivelyRootedSets edge P j := by
  classical
  ext D
  constructor
  · intro hD
    rw [Finset.mem_biUnion] at hD
    obtain ⟨S, hScandidate, hDevent⟩ := hD
    have hEvent :=
      (mem_topPartEvent (edge := edge)
        (P := P) (S := S) (D := D) (j := j)).1 hDevent
    apply
      (mem_nonProjectivelyRootedSets
        (edge := edge) (P := P) (j := j)).2
    exact
      ⟨hEvent.1,
        (not_isProjectivelyRooted_iff_exists_isTopPart
          edge P D).2 ⟨S, hEvent.2⟩⟩
  · intro hD
    have hNonrooted :=
      (mem_nonProjectivelyRootedSets
        (edge := edge) (P := P) (j := j)).1 hD
    obtain ⟨S, hStop⟩ :=
      (not_isProjectivelyRooted_iff_exists_isTopPart
        edge P D).1 hNonrooted.2
    rw [Finset.mem_biUnion]
    refine ⟨S, ?_, ?_⟩
    · apply
        (mem_topPartCandidates
          (P := P) (S := S)).2
      refine ⟨hStop.1, ?_⟩
      intro x hxS hxP
      exact
        (Finset.mem_sdiff.mp (hStop.2.1 hxS)).2 hxP
    · exact
        (mem_topPartEvent (edge := edge)
          (P := P) (S := S) (D := D) (j := j)).2
          ⟨hNonrooted.1, hStop⟩

/-- The intersection of a support family's top-part events, with the
empty-family case assigned the empty event. -/
def topPartEventIntersection
    (edge : Vertex → Vertex → Prop)
    (P : Finset Vertex) (j : ℕ)
    (C : Finset (Finset Vertex)) :
    Finset (Finset Vertex) :=
  if hC : C.Nonempty then
    C.inf' hC (topPartEvent edge P j)
  else ∅

theorem topPartEventIntersection_eq_inf'
    (edge : Vertex → Vertex → Prop)
    (P : Finset Vertex) (j : ℕ)
    {C : Finset (Finset Vertex)}
    (hC : C.Nonempty) :
    topPartEventIntersection edge P j C =
      C.inf' hC (topPartEvent edge P j) := by
  simp [topPartEventIntersection, hC]

/-- On a separated nonempty family, the total event intersection is the
event of the support union. -/
theorem topPartEventIntersection_eq_topPartEvent_supportFamilyUnion
    (edge : Vertex → Vertex → Prop)
    (P : Finset Vertex) (j : ℕ)
    {C : Finset (Finset Vertex)}
    (hC : C.Nonempty)
    (hSeparated :
      IsSeparatedSupportFamily edge C) :
    topPartEventIntersection edge P j C =
      topPartEvent edge P j
        (supportFamilyUnion C) := by
  rw [topPartEventIntersection_eq_inf'
      edge P j hC,
    inf'_topPartEvent_eq_topPartEvent_supportFamilyUnion
      edge P j hC hSeparated]

/-- On a nonseparated family of minimal candidates, the total event
intersection is empty. -/
theorem topPartEventIntersection_eq_empty_of_not_separated
    {edge : Vertex → Vertex → Prop}
    {P : Finset Vertex} {j : ℕ}
    {C : Finset (Finset Vertex)}
    (hC : C.Nonempty)
    (hCandidates :
      ∀ S ∈ C,
        S ∈ minimalTopPartCandidates edge P)
    (hNotSeparated :
      ¬ IsSeparatedSupportFamily edge C) :
    topPartEventIntersection edge P j C = ∅ := by
  rw [topPartEventIntersection_eq_inf'
      edge P j hC,
    inf'_minimalTopPartEvents_eq_empty_of_not_separated
      hC hCandidates hNotSeparated]

/-- One inclusion--exclusion term for the reduced cover indexed only by
strongly connected candidate supports. -/
def minimalTopPartInclusionExclusionTerm
    (edge : Vertex → Vertex → Prop)
    (P : Finset Vertex) (j : ℕ)
    (T :
      {T : Finset (Finset Vertex) //
        T ∈ (minimalTopPartCandidates edge P).powerset.filter
          Finset.Nonempty}) : ℤ :=
  (-1 : ℤ) ^ (T.1.card + 1) *
    (topPartEventIntersection edge P j T.1).card

/-- The inclusion--exclusion sum for the reduced strongly connected
cover. -/
def minimalTopPartInclusionExclusionSum
    (edge : Vertex → Vertex → Prop)
    (P : Finset Vertex) (j : ℕ) : ℤ :=
  ∑ T :
      {T : Finset (Finset Vertex) //
        T ∈ (minimalTopPartCandidates edge P).powerset.filter
          Finset.Nonempty},
    minimalTopPartInclusionExclusionTerm edge P j T

/-- Exact inclusion--exclusion formula using only strongly connected
candidate supports. -/
theorem nonProjectivelyRootedSets_card_eq_minimalTopPartInclusionExclusionSum
    (edge : Vertex → Vertex → Prop)
    (P : Finset Vertex) (j : ℕ) :
    ((nonProjectivelyRootedSets edge P j).card : ℤ) =
      minimalTopPartInclusionExclusionSum edge P j := by
  classical
  have h :=
    Finset.inclusion_exclusion_card_biUnion
      (minimalTopPartCandidates edge P)
      (topPartEvent edge P j)
  rw [biUnion_minimalTopPartEvents_eq_nonProjectivelyRootedSets]
    at h
  rw [h]
  unfold minimalTopPartInclusionExclusionSum
  unfold minimalTopPartInclusionExclusionTerm
  apply Finset.sum_congr rfl
  intro T hT
  rw [topPartEventIntersection_eq_inf'
    edge P j (Finset.mem_filter.mp T.2).2]

/-- The compressed inclusion--exclusion sum over nonempty separated
families, with each event intersection replaced by the event of the
support union. -/
def separatedMinimalTopPartInclusionExclusionSum
    (edge : Vertex → Vertex → Prop)
    (P : Finset Vertex) (j : ℕ) : ℤ :=
  ∑ C : SeparatedMinimalTopPartFamily edge P,
    (-1 : ℤ) ^ (C.1.card + 1) *
      (topPartEvent edge P j
        (supportFamilyUnion C.1)).card

/-- All nonseparated terms in the reduced cover vanish, while each
separated intersection is the event of its union. -/
theorem minimalTopPartInclusionExclusionSum_eq_separated
    (edge : Vertex → Vertex → Prop)
    (P : Finset Vertex) (j : ℕ) :
    minimalTopPartInclusionExclusionSum edge P j =
      separatedMinimalTopPartInclusionExclusionSum
        edge P j := by
  classical
  let raw :
      Finset (Finset (Finset Vertex)) :=
    (minimalTopPartCandidates edge P).powerset.filter
      Finset.Nonempty
  let separated :
      Finset (Finset (Finset Vertex)) :=
    separatedMinimalTopPartFamilies edge P
  unfold minimalTopPartInclusionExclusionSum
  unfold minimalTopPartInclusionExclusionTerm
  unfold separatedMinimalTopPartInclusionExclusionSum
  change
    (∑ C ∈ raw.attach,
      (-1 : ℤ) ^ (C.1.card + 1) *
        (topPartEventIntersection
          edge P j C.1).card) =
      ∑ C ∈ separated.attach,
        (-1 : ℤ) ^ (C.1.card + 1) *
          (topPartEvent edge P j
            (supportFamilyUnion C.1)).card
  calc
    (∑ C ∈ raw.attach,
        (-1 : ℤ) ^ (C.1.card + 1) *
          (topPartEventIntersection
            edge P j C.1).card) =
        ∑ C ∈ raw,
          (-1 : ℤ) ^ (C.card + 1) *
            (topPartEventIntersection
              edge P j C).card := by
      exact
        Finset.sum_attach raw
          (fun C ↦
            (-1 : ℤ) ^ (C.card + 1) *
              (topPartEventIntersection
                edge P j C).card)
    _ =
        ∑ C ∈ separated,
          (-1 : ℤ) ^ (C.card + 1) *
            (topPartEventIntersection
              edge P j C).card := by
      apply
        (Finset.sum_subset
          (s₁ := separated) ?_ ?_).symm
      · intro C hC
        have hCdata :=
          (mem_separatedMinimalTopPartFamilies.mp hC)
        exact
          Finset.mem_filter.mpr
            ⟨Finset.mem_powerset.mpr hCdata.1,
              hCdata.2.1⟩
      · intro C hCraw hCnotSeparated
        have hCdata :=
          Finset.mem_filter.mp hCraw
        have hCandidates :
            ∀ S ∈ C,
              S ∈ minimalTopPartCandidates edge P :=
          fun S hSC ↦
            (Finset.mem_powerset.mp hCdata.1) hSC
        have hNotSeparated :
            ¬ IsSeparatedSupportFamily edge C := by
          intro hSeparated
          exact hCnotSeparated
            (mem_separatedMinimalTopPartFamilies.mpr
              ⟨Finset.mem_powerset.mp hCdata.1,
                hCdata.2, hSeparated⟩)
        rw [
          topPartEventIntersection_eq_empty_of_not_separated
            hCdata.2 hCandidates hNotSeparated]
        simp
    _ =
        ∑ C ∈ separated,
          (-1 : ℤ) ^ (C.card + 1) *
            (topPartEvent edge P j
              (supportFamilyUnion C)).card := by
      apply Finset.sum_congr rfl
      intro C hC
      have hCdata :=
        (mem_separatedMinimalTopPartFamilies.mp hC)
      rw [
        topPartEventIntersection_eq_topPartEvent_supportFamilyUnion
          edge P j hCdata.2.1 hCdata.2.2]
    _ =
        ∑ C ∈ separated.attach,
          (-1 : ℤ) ^ (C.1.card + 1) *
            (topPartEvent edge P j
              (supportFamilyUnion C.1)).card := by
      exact
        (Finset.sum_attach separated
          (fun C ↦
            (-1 : ℤ) ^ (C.card + 1) *
              (topPartEvent edge P j
                (supportFamilyUnion C)).card)).symm

/-- Grouping the compressed reduced-cover sum by its globally unique
support union records exactly the number of separated strongly
connected components in the sign. -/
theorem separatedMinimalTopPartInclusionExclusionSum_group_by_union
    (edge : Vertex → Vertex → Prop)
    (P : Finset Vertex) (j : ℕ) :
    separatedMinimalTopPartInclusionExclusionSum
        edge P j =
      ∑ W :
          Set.range
            (separatedMinimalTopPartFamilyUnion edge P),
        (-1 : ℤ) ^
            (separatedSupportUnionComponentCount
              edge P W + 1) *
          (topPartEvent edge P j W.1).card := by
  classical
  unfold separatedMinimalTopPartInclusionExclusionSum
  apply
    Fintype.sum_equiv
      (separatedMinimalTopPartFamilyUnionEquiv
        edge P)
  intro C
  unfold separatedSupportUnionComponentCount
  rw [
    (separatedMinimalTopPartFamilyUnionEquiv
      edge P).symm_apply_apply]
  rfl

/-- Fully grouped inclusion--exclusion formula for nonrooted sets:
the indices are the component-separated support unions. -/
theorem nonProjectivelyRootedSets_card_eq_grouped_separated_support_unions
    (edge : Vertex → Vertex → Prop)
    (P : Finset Vertex) (j : ℕ) :
    ((nonProjectivelyRootedSets edge P j).card : ℤ) =
      ∑ W :
          Set.range
            (separatedMinimalTopPartFamilyUnion edge P),
        (-1 : ℤ) ^
            (separatedSupportUnionComponentCount
              edge P W + 1) *
          (topPartEvent edge P j W.1).card := by
  rw [
    nonProjectivelyRootedSets_card_eq_minimalTopPartInclusionExclusionSum,
    minimalTopPartInclusionExclusionSum_eq_separated,
    separatedMinimalTopPartInclusionExclusionSum_group_by_union]

/-- Paper-form grouped formula.  Each component-separated union
contributes its inclusion--exclusion sign times the forced-region
binomial count; unions larger than `j` contribute zero. -/
theorem nonProjectivelyRootedSets_card_eq_grouped_forcedRegion_choose
    (edge : Vertex → Vertex → Prop)
    (P : Finset Vertex) (j : ℕ) :
    ((nonProjectivelyRootedSets edge P j).card : ℤ) =
      ∑ W :
          Set.range
            (separatedMinimalTopPartFamilyUnion edge P),
        (-1 : ℤ) ^
            (separatedSupportUnionComponentCount
              edge P W + 1) *
          if W.1.card ≤ j then
            (Nat.choose
              (Fintype.card Vertex -
                (topPartForcedRegion edge W.1).card)
              (j - W.1.card) : ℤ)
          else 0 := by
  rw [
    nonProjectivelyRootedSets_card_eq_grouped_separated_support_unions]
  apply Finset.sum_congr rfl
  intro W hW
  obtain ⟨C, hCUnion⟩ := W.2
  have hCandidate :
      W.1 ∈ topPartCandidates P := by
    rw [← hCUnion]
    exact
      separatedMinimalTopPartFamilyUnion_mem_topPartCandidates
        edge P C
  by_cases hWj : W.1.card ≤ j
  · rw [if_pos hWj,
      topPartEvent_card_eq_choose_forcedRegion
        edge P j hCandidate hWj]
  · rw [if_neg hWj,
      topPartEvent_eq_empty_of_card_lt
        edge P j (Nat.lt_of_not_ge hWj)]
    simp

/-- Nonempty finite families of candidate top-part supports: the raw
indices in finite inclusion--exclusion. -/
def topPartIndexFamilies (P : Finset Vertex) :
    Finset (Finset (Finset Vertex)) :=
  by
    classical
    exact
      (topPartCandidates P).powerset.filter
        Finset.Nonempty

@[simp]
theorem mem_topPartIndexFamilies
    {P : Finset Vertex}
    {T : Finset (Finset Vertex)} :
    T ∈ topPartIndexFamilies P ↔
      T ⊆ topPartCandidates P ∧ T.Nonempty := by
  classical
  simp [topPartIndexFamilies]

/-- One raw inclusion--exclusion term, indexed by a nonempty family of
candidate top-part supports. -/
def topPartInclusionExclusionTerm
    (edge : Vertex → Vertex → Prop)
    (P : Finset Vertex) (j : ℕ)
    (T :
      {T : Finset (Finset Vertex) //
        T ∈ (topPartCandidates P).powerset.filter
          Finset.Nonempty}) : ℤ :=
  (-1 : ℤ) ^ (T.1.card + 1) *
    (T.1.inf'
      (Finset.mem_filter.mp T.2).2
      (topPartEvent edge P j)).card

/-- The raw finite-family inclusion--exclusion sum for nonrooted
`j`-sets. -/
def topPartInclusionExclusionSum
    (edge : Vertex → Vertex → Prop)
    (P : Finset Vertex) (j : ℕ) : ℤ :=
  ∑ T :
      {T : Finset (Finset Vertex) //
        T ∈ (topPartCandidates P).powerset.filter
          Finset.Nonempty},
    topPartInclusionExclusionTerm edge P j T

/-- Exact raw inclusion--exclusion formula for non-projectively-rooted
sets. -/
theorem nonProjectivelyRootedSets_card_eq_inclusionExclusionSum
    (edge : Vertex → Vertex → Prop)
    (P : Finset Vertex) (j : ℕ) :
    ((nonProjectivelyRootedSets edge P j).card : ℤ) =
      topPartInclusionExclusionSum edge P j := by
  classical
  have h :=
    Finset.inclusion_exclusion_card_biUnion
      (topPartCandidates P)
      (topPartEvent edge P j)
  rw [biUnion_topPartEvents_eq_nonProjectivelyRootedSets] at h
  simpa only [topPartInclusionExclusionSum,
    topPartInclusionExclusionTerm]
    using h

/-- The exact finite-family input needed to compare the two raw
inclusion--exclusion sums.  In an AR application the equivalence and term
identity are to be supplied by mesh rotation (possibly after compressing
families to component-separated unions). -/
structure TopPartInclusionExclusionMatching
    (qEdge sEdge : Vertex → Vertex → Prop)
    (P I : Finset Vertex) (j : ℕ) where
  indexEquiv :
    {T : Finset (Finset Vertex) //
      T ∈ (topPartCandidates P).powerset.filter
        Finset.Nonempty} ≃
      {T : Finset (Finset Vertex) //
        T ∈ (topPartCandidates I).powerset.filter
          Finset.Nonempty}
  term_eq :
    ∀ T,
      topPartInclusionExclusionTerm
          qEdge P j T =
        topPartInclusionExclusionTerm
          sEdge I j (indexEquiv T)

/-- Matching every raw inclusion--exclusion term gives equality of the
two sums. -/
theorem topPartInclusionExclusionSum_eq_of_matching
    {qEdge sEdge : Vertex → Vertex → Prop}
    {P I : Finset Vertex} {j : ℕ}
    (M :
      TopPartInclusionExclusionMatching
        qEdge sEdge P I j) :
    topPartInclusionExclusionSum qEdge P j =
      topPartInclusionExclusionSum sEdge I j := by
  classical
  unfold topPartInclusionExclusionSum
  apply Fintype.sum_equiv M.indexEquiv
  intro T
  exact M.term_eq T

omit [DecidableEq Vertex] in
/-- Equal nonrooted counts imply equal rooted counts because both
families partition the same collection of `j`-subsets. -/
theorem projectivelyRootedSets_card_eq_of_nonrooted_card_eq
    {qEdge sEdge : Vertex → Vertex → Prop}
    {P I : Finset Vertex} {j : ℕ}
    (hnonrooted :
      (nonProjectivelyRootedSets qEdge P j).card =
        (nonProjectivelyRootedSets sEdge I j).card) :
    (projectivelyRootedSets qEdge P j).card =
      (projectivelyRootedSets sEdge I j).card := by
  classical
  have hq :=
    Finset.card_filter_add_card_filter_not
      (s := setsOfCard (Vertex := Vertex) j)
      (IsProjectivelyRooted qEdge P)
  have hs :=
    Finset.card_filter_add_card_filter_not
      (s := setsOfCard (Vertex := Vertex) j)
      (IsProjectivelyRooted sEdge I)
  have hq' :
      (projectivelyRootedSets qEdge P j).card +
          (nonProjectivelyRootedSets qEdge P j).card =
        (setsOfCard (Vertex := Vertex) j).card := by
    simpa only [projectivelyRootedSets,
      nonProjectivelyRootedSets] using hq
  have hs' :
      (projectivelyRootedSets sEdge I j).card +
          (nonProjectivelyRootedSets sEdge I j).card =
        (setsOfCard (Vertex := Vertex) j).card := by
    simpa only [projectivelyRootedSets,
      nonProjectivelyRootedSets] using hs
  omega

/-- A termwise matching of the finite inclusion--exclusion data implies
equality of projectively rooted `j`-set counts. -/
theorem projectivelyRootedSets_card_eq_of_inclusionExclusionMatching
    {qEdge sEdge : Vertex → Vertex → Prop}
    {P I : Finset Vertex} {j : ℕ}
    (M :
      TopPartInclusionExclusionMatching
        qEdge sEdge P I j) :
    (projectivelyRootedSets qEdge P j).card =
      (projectivelyRootedSets sEdge I j).card := by
  apply projectivelyRootedSets_card_eq_of_nonrooted_card_eq
  have hq :=
    nonProjectivelyRootedSets_card_eq_inclusionExclusionSum
      qEdge P j
  have hs :=
    nonProjectivelyRootedSets_card_eq_inclusionExclusionSum
      sEdge I j
  have hsum :=
    topPartInclusionExclusionSum_eq_of_matching M
  exact_mod_cast hq.trans (hsum.trans hs.symm)

/-- Injectively corooted vertex sets of cardinality `j`, enumerated by
viewing the graph with its edge relation reversed. -/
def injectivelyCorootedSets
    (edge : Vertex → Vertex → Prop)
    (I : Finset Vertex) (j : ℕ) :
    Finset (Finset Vertex) :=
  projectivelyRootedSets (fun x y ↦ edge y x) I j

omit [DecidableEq Vertex] in
@[simp]
theorem mem_injectivelyCorootedSets
    {edge : Vertex → Vertex → Prop}
    {I : Finset Vertex} {j : ℕ} {D : Finset Vertex} :
    D ∈ injectivelyCorootedSets edge I j ↔
      D.card = j ∧ IsInjectivelyCorooted edge I D := by
  simp [injectivelyCorootedSets,
    IsInjectivelyCorooted]

/-- Direct rooted-versus-corooted endpoint.  A matching compares the
projective-side top-part inclusion--exclusion data with the
injective-side data for the reversed relation. -/
theorem projectivelyRootedSets_card_eq_injectivelyCorootedSets_card_of_matching
    {qEdge sEdge : Vertex → Vertex → Prop}
    {P I : Finset Vertex} {j : ℕ}
    (M :
      TopPartInclusionExclusionMatching
        qEdge (fun x y ↦ sEdge y x) P I j) :
    (projectivelyRootedSets qEdge P j).card =
      (injectivelyCorootedSets sEdge I j).card :=
  projectivelyRootedSets_card_eq_of_inclusionExclusionMatching M

/--
A matching of the globally grouped top-part supports on two directed
graphs. These are exactly the statistics occurring in the compressed
inclusion--exclusion formula:

* the number of strongly connected components;
* the size of their support union;
* the size of the forced region `W ∪ N⁻(W)`.
-/
structure GroupedTopPartMatching
    (qEdge sEdge : Vertex → Vertex → Prop)
    (P I : Finset Vertex) where
  equiv :
    Set.range
        (separatedMinimalTopPartFamilyUnion qEdge P) ≃
      Set.range
        (separatedMinimalTopPartFamilyUnion sEdge I)
  componentCount_eq :
    ∀ W,
      separatedSupportUnionComponentCount qEdge P W =
        separatedSupportUnionComponentCount sEdge I (equiv W)
  supportCard_eq :
    ∀ W, W.1.card = (equiv W).1.card
  forcedRegionCard_eq :
    ∀ W,
      (topPartForcedRegion qEdge W.1).card =
        (topPartForcedRegion sEdge (equiv W).1).card

/--
A matching of the three grouped statistics identifies the two nonrooted
counts in every cardinality.
-/
theorem nonProjectivelyRootedSets_card_eq_of_groupedMatching
    {qEdge sEdge : Vertex → Vertex → Prop}
    {P I : Finset Vertex}
    (M : GroupedTopPartMatching qEdge sEdge P I)
    (j : ℕ) :
    (nonProjectivelyRootedSets qEdge P j).card =
      (nonProjectivelyRootedSets sEdge I j).card := by
  have hq :=
    nonProjectivelyRootedSets_card_eq_grouped_forcedRegion_choose
      qEdge P j
  have hs :=
    nonProjectivelyRootedSets_card_eq_grouped_forcedRegion_choose
      sEdge I j
  have hsum :
      (∑ W :
          Set.range
            (separatedMinimalTopPartFamilyUnion qEdge P),
        (-1 : ℤ) ^
            (separatedSupportUnionComponentCount qEdge P W + 1) *
          if W.1.card ≤ j then
            (Nat.choose
              (Fintype.card Vertex -
                (topPartForcedRegion qEdge W.1).card)
              (j - W.1.card) : ℤ)
          else 0) =
      ∑ W :
          Set.range
            (separatedMinimalTopPartFamilyUnion sEdge I),
        (-1 : ℤ) ^
            (separatedSupportUnionComponentCount sEdge I W + 1) *
          if W.1.card ≤ j then
            (Nat.choose
              (Fintype.card Vertex -
                (topPartForcedRegion sEdge W.1).card)
              (j - W.1.card) : ℤ)
          else 0 := by
    apply Fintype.sum_equiv M.equiv
    intro W
    rw [M.componentCount_eq W, M.supportCard_eq W,
      M.forcedRegionCard_eq W]
  exact_mod_cast hq.trans (hsum.trans hs.symm)

/--
After reversing the second edge relation, a grouped matching gives the
rooted-versus-corooted equality needed in the manuscript.
-/
theorem projectivelyRootedSets_card_eq_injectivelyCorootedSets_card_of_groupedMatching
    {qEdge sEdge : Vertex → Vertex → Prop}
    {P I : Finset Vertex}
    (M :
      GroupedTopPartMatching
        qEdge (fun x y ↦ sEdge y x) P I)
    (j : ℕ) :
    (projectivelyRootedSets qEdge P j).card =
      (injectivelyCorootedSets sEdge I j).card := by
  apply projectivelyRootedSets_card_eq_of_nonrooted_card_eq
  exact
    nonProjectivelyRootedSets_card_eq_of_groupedMatching
      M j

end InclusionExclusion

end QuotientSubmoduleEquidistribution.RootedDigraph
