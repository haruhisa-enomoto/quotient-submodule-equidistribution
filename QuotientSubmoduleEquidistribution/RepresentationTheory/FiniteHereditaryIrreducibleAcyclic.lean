import QuotientSubmoduleEquidistribution.RepresentationTheory.ARLocalRestrictions
import QuotientSubmoduleEquidistribution.RepresentationTheory.HereditaryThreeSimpleUnconditional
import QuotientSubmoduleEquidistribution.RepresentationTheory.IrreducibleReachability
import QuotientSubmoduleEquidistribution.RepresentationDirected.IrreducibleDimensionGrowth

/-!
# Acyclicity of the finite hereditary AR quiver

This file isolates the classification-free Auslander--Reiten argument used
for representation-finite hereditary algebras.  Its local hereditary input
is that an irreducible predecessor of an indecomposable projective is again
projective.  Mesh rotation and projective rootedness then put every vertex
on a projective-to-injective translation chain and exclude oriented cycles.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

universe u v

variable {K R : Type u} [Field K] [Ring R] [Algebra K R]
  [FiniteDimensional K R] [IsNoetherianRing R]
  {ι : Type v} [Fintype ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)

attribute [local instance] FintypeCat.fintype

namespace FiniteARTranslationData

variable (AR : σ.FiniteARTranslationData)

/-- The only local hereditary property needed by the translation-quiver
argument. -/
def IrreduciblePredecessorsOfProjectivesAreProjective
    (_AR : σ.FiniteARTranslationData) : Prop :=
  ∀ {x p : ι}, Projective (σ.obj p) →
    σ.irreducibleEdge x p → Projective (σ.obj x)

omit [Fintype ι] in
/-- Finite left heredity supplies the local projective-predecessor
property: an irreducible map into a projective cannot be epic, hence is
monic, and a submodule of a finitely generated projective is projective. -/
theorem irreduciblePredecessorsOfProjectivesAreProjective_of_finitelyGeneratedLeftHereditary
    (hHereditary :
      FaithfulCore.ConnectedSmallCore.FinitelyGeneratedLeftHereditary R) :
    AR.IrreduciblePredecessorsOfProjectivesAreProjective σ := by
  intro x p hp hxp
  obtain ⟨f, hf⟩ := hxp
  rcases
      _root_.QuotientSubmoduleEquidistribution.RepresentationDirected.mono_or_epi_of_isIrreducibleMorphism
        hf with hmono | hepi
  · letI : Mono f := hmono
    exact
      _root_.QuotientSubmoduleEquidistribution.HereditaryThreeSimpleUnconditional.fgProjective_of_mono_to_fgProjective_of_finitelyGeneratedLeftHereditary
          hHereditary f hmono hp
  · letI : Epi f := hepi
    obtain ⟨s, hs⟩ := Projective.factors (𝟙 (σ.obj p)) f
    exact (hf.not_isSplitEpi
      (IsSplitEpi.mk' { section_ := s, id := hs })).elim

/-- A vertex lying on one of the finite inverse-AR-translation chains
starting at an indecomposable projective. -/
def OnProjectiveChain (x : ι) : Prop :=
  let T := AR.boundaryTranslationChainData σ
  ∃ (p : ι) (hp : Projective (σ.obj p)) (n : ℕ),
    n ≤ T.firstTargetIndex p hp ∧ T.successor^[n] p = x

/-- Every projective vertex starts its own translation chain. -/
theorem onProjectiveChain_of_projective {p : ι}
    (hp : Projective (σ.obj p)) : AR.OnProjectiveChain σ p := by
  let T := AR.boundaryTranslationChainData σ
  exact ⟨p, hp, 0, Nat.zero_le _, rfl⟩

/-- A noninjective point on a projective chain may be advanced by one
inverse-translation step while remaining on such a chain. -/
theorem onProjectiveChain_successor_of_noninjective {x : ι}
    (hx : AR.OnProjectiveChain σ x)
    (hxi : ¬ Injective (σ.obj x)) :
    AR.OnProjectiveChain σ
      ((AR.boundaryTranslationChainData σ).successor x) := by
  let T := AR.boundaryTranslationChainData σ
  obtain ⟨p, hp, n, hn, rfl⟩ := hx
  change n ≤ T.firstTargetIndex p hp at hn
  have hnlt : n < T.firstTargetIndex p hp := by
    have hne : n ≠ T.firstTargetIndex p hp := by
      intro heq
      apply hxi
      rw [heq]
      exact T.firstTargetIndex_spec p hp
    omega
  refine ⟨p, hp, n + 1, ?_, ?_⟩
  · change n + 1 ≤ T.firstTargetIndex p hp
    omega
  change T.successor^[n + 1] p = T.successor (T.successor^[n] p)
  exact Function.iterate_succ_apply' T.successor n p

/-- Inverse AR translation followed by the boundary-chain successor
returns the original nonprojective label. -/
theorem successor_arTranslationLabel
    (x : ι) (hx : ¬ Projective (σ.obj x)) :
    (AR.boundaryTranslationChainData σ).successor
        (AR.arTranslation σ ⟨x, hx⟩).1 = x := by
  classical
  let T := AR.boundaryTranslationChainData σ
  change T.successor (AR.arTranslationEquiv σ ⟨x, hx⟩).1 = x
  change
    (if h : Injective
        (σ.obj (AR.arTranslationEquiv σ ⟨x, hx⟩).1) then
      (AR.arTranslationEquiv σ ⟨x, hx⟩).1
    else
      ((AR.arTranslationEquiv σ).symm
        ⟨(AR.arTranslationEquiv σ ⟨x, hx⟩).1, h⟩).1) = x
  rw [dif_neg (AR.arTranslationEquiv σ ⟨x, hx⟩).2]
  exact congrArg Subtype.val
    ((AR.arTranslationEquiv σ).symm_apply_apply ⟨x, hx⟩)

/-- Predecessors of projective translation chains remain on projective
translation chains.  The proof is induction on the chain position and two
successive mesh rotations. -/
theorem onProjectiveChain_of_irreducible_predecessor
    (hlocal : AR.IrreduciblePredecessorsOfProjectivesAreProjective σ) :
    ∀ (n : ℕ) (p : ι) (hp : Projective (σ.obj p)),
      n ≤ (AR.boundaryTranslationChainData σ).firstTargetIndex p hp →
      ∀ {a : ι},
        (AR.boundaryTranslationChainData σ).successor^[n] p = a →
        ∀ {c : ι}, σ.irreducibleEdge c a →
          AR.OnProjectiveChain σ c
  | 0, p, hp, _hn, a, ha, c, hca => by
      subst a
      exact AR.onProjectiveChain_of_projective σ (hlocal hp hca)
  | n + 1, p, hp, hn, a, ha, c, hca => by
      let T := AR.boundaryTranslationChainData σ
      let q : ι := T.successor^[n] p
      change n + 1 ≤ T.firstTargetIndex p hp at hn
      have hnlt : n < T.firstTargetIndex p hp := by omega
      have hqni : ¬ Injective (σ.obj q) :=
        T.not_mem_target_before_firstTargetIndex p hp hnlt
      have haSucc : T.successor q = a := by
        exact (Function.iterate_succ_apply' T.successor n p).symm.trans ha
      subst a
      have hanp : ¬ Projective (σ.obj (T.successor q)) := by
        exact T.successor_not_mem_source_of_not_mem_target hqni
      have htaua :
          (AR.arTranslation σ ⟨T.successor q, hanp⟩).1 = q := by
        exact AR.arTranslation_successor_of_noninjective σ q hqni
      have hca' : σ.irreducibleEdge c (T.successor q) := by
        rw [haSucc]
        exact hca
      have hqc : σ.irreducibleEdge q c := by
        have hraw := (AR.arTranslation_incidence σ
          ⟨T.successor q, hanp⟩ c).1 hca'
        simpa only [irreducibleEdge, htaua] using hraw
      by_cases hcp : Projective (σ.obj c)
      · exact AR.onProjectiveChain_of_projective σ hcp
      · have htaucq :
            σ.irreducibleEdge (AR.arTranslation σ ⟨c, hcp⟩).1 q := by
          apply (AR.arTranslation_incidence σ ⟨c, hcp⟩ q).1
          exact hqc
        have htaucOn :
            AR.OnProjectiveChain σ
              (AR.arTranslation σ ⟨c, hcp⟩).1 :=
          onProjectiveChain_of_irreducible_predecessor
            hlocal n p hp (by
              change n ≤ T.firstTargetIndex p hp
              omega) rfl htaucq
        have hnext := AR.onProjectiveChain_successor_of_noninjective σ
          htaucOn (AR.arTranslation σ ⟨c, hcp⟩).2
        simpa [AR.successor_arTranslationLabel σ c hcp] using hnext
termination_by n => n

/-- Projective-chain membership is forward closed under irreducible
arrows. -/
theorem onProjectiveChain_of_irreducible_successor
    (hlocal : AR.IrreduciblePredecessorsOfProjectivesAreProjective σ)
    {a b : ι} (ha : AR.OnProjectiveChain σ a)
    (hab : σ.irreducibleEdge a b) :
    AR.OnProjectiveChain σ b := by
  by_cases hbp : Projective (σ.obj b)
  · exact AR.onProjectiveChain_of_projective σ hbp
  · have htaupa :
        σ.irreducibleEdge (AR.arTranslation σ ⟨b, hbp⟩).1 a := by
      apply (AR.arTranslation_incidence σ ⟨b, hbp⟩ a).1
      exact hab
    obtain ⟨p, hp, n, hn, haeq⟩ := ha
    have htauOn := AR.onProjectiveChain_of_irreducible_predecessor σ
      hlocal n p hp hn haeq htaupa
    have hnext := AR.onProjectiveChain_successor_of_noninjective σ
      htauOn (AR.arTranslation σ ⟨b, hbp⟩).2
    simpa [AR.successor_arTranslationLabel σ b hbp] using hnext

include K in
/-- Projective rootedness and the local hereditary boundary condition put
every AR vertex on a projective translation chain. -/
theorem onProjectiveChain_all
    (hlocal : AR.IrreduciblePredecessorsOfProjectivesAreProjective σ)
    (x : ι) : AR.OnProjectiveChain σ x := by
  have hroot := isProjectivelyRooted_univ (K := K) σ x
    (Finset.mem_univ x)
  obtain ⟨p, hp, _hpuniv, hpx⟩ := hroot
  have hp' : Projective (σ.obj p) := by
    simpa [projectiveLabelFinset] using hp
  have hstart : AR.OnProjectiveChain σ p :=
    AR.onProjectiveChain_of_projective σ hp'
  have forward : ∀ {a b : ι},
      Relation.ReflTransGen
          (QuotientSubmoduleEquidistribution.RootedDigraph.InsideEdge
            σ.irreducibleEdge Finset.univ) a b →
        AR.OnProjectiveChain σ a → AR.OnProjectiveChain σ b := by
    intro a b hab ha
    induction hab with
    | refl => exact ha
    | @tail b c hab hbc ih =>
        exact AR.onProjectiveChain_of_irreducible_successor σ
          hlocal ih hbc.2.2
  exact forward hpx hstart

omit [Fintype ι] in
/-- A nonempty irreducible path ending at a projective strictly increases
ground-field dimension. -/
theorem groundFinrank_lt_of_transGen_irreducible_to_projective
    (hlocal : AR.IrreduciblePredecessorsOfProjectivesAreProjective σ)
    {a p : ι} (hap : Relation.TransGen σ.irreducibleEdge a p)
    (hp : Projective (σ.obj p)) :
    QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
        (K := K) (σ.obj a) <
      QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
        (K := K) (σ.obj p) := by
  induction hap with
  | single h =>
      exact groundFinrank_lt_of_irreducible_to_projective
        (K := K) σ hp h
  | @tail b c hab hbc ih =>
      have hb : Projective (σ.obj b) := hlocal hp hbc
      exact lt_trans (ih hb)
        (groundFinrank_lt_of_irreducible_to_projective
          (K := K) σ hp hbc)

omit [Fintype ι] in
/-- AR translation carries an irreducible arrow between nonprojective
vertices to an irreducible arrow with the same orientation. -/
theorem irreducibleEdge_arTranslation
    {a b : ι} (ha : ¬ Projective (σ.obj a))
    (hb : ¬ Projective (σ.obj b))
    (hab : σ.irreducibleEdge a b) :
    σ.irreducibleEdge
      (AR.arTranslation σ ⟨a, ha⟩).1
      (AR.arTranslation σ ⟨b, hb⟩).1 := by
  have hba :
      σ.irreducibleEdge (AR.arTranslation σ ⟨b, hb⟩).1 a :=
    (AR.arTranslation_incidence σ ⟨b, hb⟩ a).1 hab
  exact (AR.arTranslation_incidence σ ⟨a, ha⟩
    (AR.arTranslation σ ⟨b, hb⟩).1).1 hba

omit [Fintype ι] in
/-- If the source of an irreducible path is nonprojective, every later
vertex is nonprojective and simultaneous AR translation gives another
irreducible path. -/
theorem transGen_arTranslation_of_source_nonprojective
    (hlocal : AR.IrreduciblePredecessorsOfProjectivesAreProjective σ)
    {a b : ι} (ha : ¬ Projective (σ.obj a))
    (hab : Relation.TransGen σ.irreducibleEdge a b) :
    ∃ hb : ¬ Projective (σ.obj b),
      Relation.TransGen σ.irreducibleEdge
        (AR.arTranslation σ ⟨a, ha⟩).1
        (AR.arTranslation σ ⟨b, hb⟩).1 := by
  induction hab generalizing ha with
  | @single b h =>
      have hb : ¬ Projective (σ.obj b) := by
        intro hbp
        exact ha (hlocal hbp h)
      exact ⟨hb, Relation.TransGen.single
        (AR.irreducibleEdge_arTranslation σ ha hb h)⟩
  | @tail b c hab hbc ih =>
      obtain ⟨hb, htranslated⟩ := ih ha
      have hc : ¬ Projective (σ.obj c) := by
        intro hcp
        exact hb (hlocal hcp hbc)
      exact ⟨hc, Relation.TransGen.tail htranslated
        (AR.irreducibleEdge_arTranslation σ hb hc hbc)⟩

include K in
/-- No vertex on a projective translation chain supports an oriented
irreducible cycle. -/
theorem not_transGen_irreducible_self_of_onProjectiveChain
    (hlocal : AR.IrreduciblePredecessorsOfProjectivesAreProjective σ)
    {x : ι} (hx : AR.OnProjectiveChain σ x) :
    ¬ Relation.TransGen σ.irreducibleEdge x x := by
  let T := AR.boundaryTranslationChainData σ
  obtain ⟨p, hp, n, hn, hpx⟩ := hx
  induction n generalizing x with
  | zero =>
      intro hcycle
      have hxp : x = p := by simpa using hpx.symm
      subst x
      have hlt :=
        groundFinrank_lt_of_transGen_irreducible_to_projective (K := K) σ AR
          hlocal hcycle hp
      exact (lt_irrefl _ hlt)
  | succ n ih =>
      intro hcycle
      change n + 1 ≤ T.firstTargetIndex p hp at hn
      have hnlt : n < T.firstTargetIndex p hp := by omega
      have hqni : ¬ Injective (σ.obj (T.successor^[n] p)) :=
        T.not_mem_target_before_firstTargetIndex p hp hnlt
      have hxSucc : T.successor (T.successor^[n] p) = x :=
        (Function.iterate_succ_apply' T.successor n p).symm.trans hpx
      subst x
      have hxnp :
          ¬ Projective (σ.obj (T.successor (T.successor^[n] p))) :=
        T.successor_not_mem_source_of_not_mem_target hqni
      have hcycle' :
          Relation.TransGen σ.irreducibleEdge
            (T.successor (T.successor^[n] p))
            (T.successor (T.successor^[n] p)) := by
        simpa only [Function.iterate_succ_apply'] using hcycle
      obtain ⟨hxnp', htranslated⟩ :=
        AR.transGen_arTranslation_of_source_nonprojective σ
          hlocal hxnp hcycle'
      have htaux := AR.arTranslation_successor_of_noninjective σ
        (T.successor^[n] p) hqni
      rw [htaux] at htranslated
      exact (ih (by
        change n ≤ T.firstTargetIndex p hp
        omega) rfl) htranslated

include K in
/-- The irreducible AR digraph of a finite skeleton is acyclic under the
local hereditary projective-predecessor property. -/
theorem irreducibleEdge_acyclic
    (hlocal : AR.IrreduciblePredecessorsOfProjectivesAreProjective σ) :
    ∀ x : ι, ¬ Relation.TransGen σ.irreducibleEdge x x := by
  intro x
  exact not_transGen_irreducible_self_of_onProjectiveChain (K := K) σ AR hlocal
    (onProjectiveChain_all (K := K) σ AR hlocal x)

end FiniteARTranslationData

include K in
/-- The classification-free AR argument only needs the local statement that
irreducible predecessors of projectives are projective. -/
theorem hasAcyclicNonzeroNonisomorphisms_of_irreduciblePredecessorsOfProjectivesAreProjective
    (hlocal : FiniteARTranslationData.IrreduciblePredecessorsOfProjectivesAreProjective
        σ (σ.finiteDimensionalARTranslationData K R)) :
    QuotientSubmoduleEquidistribution.RepresentationDirected.HasAcyclicNonzeroNonisomorphisms σ := by
  let AR := σ.finiteDimensionalARTranslationData K R
  apply
    IrreducibleReachability.finiteDimensional_hasAcyclicNonzeroNonisomorphisms_of_irreducibleEdge_acyclic
      (K := K) σ
  exact AR.irreducibleEdge_acyclic (K := K) σ hlocal

include K in
/-- A finite-dimensional representation-finite left-hereditary algebra is
representation-directed, without using Dynkin classification. -/
theorem hasAcyclicNonzeroNonisomorphisms_of_finitelyGeneratedLeftHereditary
    (hHereditary :
      FaithfulCore.ConnectedSmallCore.FinitelyGeneratedLeftHereditary R) :
    QuotientSubmoduleEquidistribution.RepresentationDirected.HasAcyclicNonzeroNonisomorphisms σ := by
  let AR := σ.finiteDimensionalARTranslationData K R
  apply
    IrreducibleReachability.finiteDimensional_hasAcyclicNonzeroNonisomorphisms_of_irreducibleEdge_acyclic
      (K := K) σ
  apply AR.irreducibleEdge_acyclic (K := K) σ
  exact
    AR.irreduciblePredecessorsOfProjectivesAreProjective_of_finitelyGeneratedLeftHereditary
      σ hHereditary

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
