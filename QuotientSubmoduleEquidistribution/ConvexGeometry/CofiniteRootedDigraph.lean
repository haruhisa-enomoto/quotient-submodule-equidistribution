import QuotientSubmoduleEquidistribution.Combinatorics.RootedDigraph
import QuotientSubmoduleEquidistribution.ConvexGeometry.CofiniteRooted

/-!
# Directed-rooted input for cofinite closure counts

This file connects the directed-graph rooted-set count to the abstract
rooted/bad-rooted cofinite endpoint.  A grouped top-part matching discharges
the rooted-count field; only the closure characterizations and equality of
the genuinely bad rooted families remain as inputs.
-/

noncomputable section

open Set

namespace QuotientSubmoduleEquidistribution.SetClosure

universe u

variable {E : Type u} [Fintype E] [DecidableEq E]

/-- Closure characterizations by projective rootedness, injective
corootedness, and matched bad events assemble the abstract cofinite input.

The grouped matching is independent of the deletion cardinality and hence
can be reused at colevels three and four. -/
def rootedBadCofiniteInput_of_groupedTopPartMatching
    (qClosure sClosure : SetClosure E)
    (qEdge sEdge : E → E → Prop)
    (P I : Finset E)
    (M :
      QuotientSubmoduleEquidistribution.RootedDigraph.GroupedTopPartMatching
        qEdge (fun x y ↦ sEdge y x) P I)
    (j : ℕ)
    (qBad sBad : Finset E → Prop)
    (qClosedComplement_iff :
      ∀ {D : Finset E}, D.card = j →
        (qClosure.IsClosed ((D : Set E)ᶜ) ↔
          QuotientSubmoduleEquidistribution.RootedDigraph.IsProjectivelyRooted qEdge P D ∧
            ¬ qBad D))
    (sClosedComplement_iff :
      ∀ {D : Finset E}, D.card = j →
        (sClosure.IsClosed ((D : Set E)ᶜ) ↔
          QuotientSubmoduleEquidistribution.RootedDigraph.IsInjectivelyCorooted sEdge I D ∧
            ¬ sBad D))
    (bad_rooted_card_eq :
      (badRootedDeletions
          (QuotientSubmoduleEquidistribution.RootedDigraph.IsProjectivelyRooted qEdge P)
          qBad j).card =
        (badRootedDeletions
          (QuotientSubmoduleEquidistribution.RootedDigraph.IsInjectivelyCorooted sEdge I)
          sBad j).card) :
    RootedBadCofiniteInput qClosure sClosure j where
  qRooted :=
    QuotientSubmoduleEquidistribution.RootedDigraph.IsProjectivelyRooted qEdge P
  sRooted :=
    QuotientSubmoduleEquidistribution.RootedDigraph.IsInjectivelyCorooted sEdge I
  qBad := qBad
  sBad := sBad
  qClosedComplement_iff := qClosedComplement_iff
  sClosedComplement_iff := sClosedComplement_iff
  rooted_card_eq := by
    calc
      (rootedDeletions
          (QuotientSubmoduleEquidistribution.RootedDigraph.IsProjectivelyRooted qEdge P)
          j).card =
          (QuotientSubmoduleEquidistribution.RootedDigraph.projectivelyRootedSets
            qEdge P j).card := by
        congr 1
      _ =
          (QuotientSubmoduleEquidistribution.RootedDigraph.injectivelyCorootedSets
            sEdge I j).card :=
        QuotientSubmoduleEquidistribution.RootedDigraph.projectivelyRootedSets_card_eq_injectivelyCorootedSets_card_of_groupedMatching
          M j
      _ =
          (rootedDeletions
            (QuotientSubmoduleEquidistribution.RootedDigraph.IsInjectivelyCorooted sEdge I)
            j).card := by
        congr 1
  bad_rooted_card_eq := bad_rooted_card_eq

/-- Paper-facing colevel equality after the grouped rooted count has been
eliminated. -/
theorem levelCount_card_sub_eq_of_groupedTopPartMatching
    (qClosure sClosure : SetClosure E)
    (qEdge sEdge : E → E → Prop)
    (P I : Finset E)
    (M :
      QuotientSubmoduleEquidistribution.RootedDigraph.GroupedTopPartMatching
        qEdge (fun x y ↦ sEdge y x) P I)
    (j : ℕ) (hj : j ≤ Nat.card E)
    (qBad sBad : Finset E → Prop)
    (qClosedComplement_iff :
      ∀ {D : Finset E}, D.card = j →
        (qClosure.IsClosed ((D : Set E)ᶜ) ↔
          QuotientSubmoduleEquidistribution.RootedDigraph.IsProjectivelyRooted qEdge P D ∧
            ¬ qBad D))
    (sClosedComplement_iff :
      ∀ {D : Finset E}, D.card = j →
        (sClosure.IsClosed ((D : Set E)ᶜ) ↔
          QuotientSubmoduleEquidistribution.RootedDigraph.IsInjectivelyCorooted sEdge I D ∧
            ¬ sBad D))
    (bad_rooted_card_eq :
      (badRootedDeletions
          (QuotientSubmoduleEquidistribution.RootedDigraph.IsProjectivelyRooted qEdge P)
          qBad j).card =
        (badRootedDeletions
          (QuotientSubmoduleEquidistribution.RootedDigraph.IsInjectivelyCorooted sEdge I)
          sBad j).card) :
    qClosure.levelCount (Nat.card E - j) =
      sClosure.levelCount (Nat.card E - j) := by
  exact
    levelCount_card_sub_eq_of_rootedBadCofiniteInput
      qClosure sClosure j hj <|
        rootedBadCofiniteInput_of_groupedTopPartMatching
          qClosure sClosure qEdge sEdge P I M j qBad sBad
            qClosedComplement_iff sClosedComplement_iff
              bad_rooted_card_eq

end QuotientSubmoduleEquidistribution.SetClosure
