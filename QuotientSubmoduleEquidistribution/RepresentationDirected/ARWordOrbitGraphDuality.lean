import QuotientSubmoduleEquidistribution.RepresentationDirected.ARWordDuality
import QuotientSubmoduleEquidistribution.RepresentationDirected.PositionedQuotientProfile
import QuotientSubmoduleEquidistribution.RepresentationDirected.CoxeterEdgeDeletion

/-!
# Orbit-graph and positioned-word transport under opposite duality

This file proves that an aligned biduality reverses irreducible arrows and
identifies the two Auslander--Reiten orbit graphs.  It then transports the
simply-laced Coxeter data, reduced words, local subwords, and the positioned
quotient-closure correspondence across the induced orbit-label equivalence.

All arguments are categorical and combinatorial.  No concrete algebra,
quiver presentation, module enumeration, or classification is used.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.RepresentationDirected.OrbitGraphDuality

open QuotientSubmoduleEquidistribution
open QuotientSubmoduleEquidistribution.RepresentationDirected.FixedWord
open QuotientSubmoduleEquidistribution.RepresentationDirected
open QuotientSubmoduleEquidistribution.RepresentationDirected.ARWordDuality
open QuotientSubmoduleEquidistribution.RepresentationDirected.ARWord.SelectedSegments
open QuotientSubmoduleEquidistribution.RepresentationDirected.DirectedAROrbit
open QuotientSubmoduleEquidistribution.RepresentationDirected.DirectedAROrbit.OrderedARWord
open QuotientSubmoduleEquidistribution.RepresentationDirected.DirectedQuotientProfile.Positioned
open QuotientSubmoduleEquidistribution.RepresentationDirected.DirectedSorting
open QuotientSubmoduleEquidistribution.RepresentationDirected.FixedWordSubwords
open QuotientSubmoduleEquidistribution.RepresentationDirected.PrincipalPositivity
open QuotientSubmoduleEquidistribution.RepresentationDirected.SegmentReducedness
open QuotientSubmoduleEquidistribution.RepresentationDirected.SimpleGraphCoxeter

/-! ## Irreducible arrows and orbit graphs under an aligned biduality -/

universe uR uS uI uK

variable
    {R : Type uR} [Ring R] [IsNoetherianRing R]
    {S : Type uS} [Ring S] [IsNoetherianRing S]
    {I : Type uI} {Kappa : Type uK}
    (sigma : IndecomposableSkeleton.{uR, uI, uR} R I)
    (tau : IndecomposableSkeleton.{uS, uK, uS} S Kappa)

/-- The contravariant image of a morphism, with both endpoints aligned to
the chosen target skeleton. -/
def dualMorphism
    (D : tau.AlignedAntiEquivalence sigma)
    {u v : Kappa} (f : tau.obj u ⟶ tau.obj v) :
    sigma.obj (D.labelEquiv v) ⟶ sigma.obj (D.labelEquiv u) :=
  (D.objIso v).inv ≫ D.categoryEquiv.functor.map f.op ≫
    (D.objIso u).hom

/-- An aligned anti-equivalence sends every irreducible arrow to an
irreducible arrow in the reverse direction. -/
theorem isIrreducible_dualMorphism
    (D : tau.AlignedAntiEquivalence sigma)
    {u v : Kappa} {f : tau.obj u ⟶ tau.obj v}
    (hf : IsIrreducibleMorphism f) :
    IsIrreducibleMorphism (dualMorphism sigma tau D f) := by
  exact IsIrreducibleMorphism.postcomp_iso
    (IsIrreducibleMorphism.precomp_iso
      (IsIrreducibleMorphism.map_equivalence
        (IsIrreducibleMorphism.op hf) D.categoryEquiv)
      (D.objIso v).symm)
    (D.objIso u)

/-- One-way existence form of contravariant irreducibility transport. -/
theorem hasIrreducibleMorphism_dual
    (D : tau.AlignedAntiEquivalence sigma) (u v : Kappa) :
    HasIrreducibleMorphism (tau.obj u) (tau.obj v) →
      HasIrreducibleMorphism
        (sigma.obj (D.labelEquiv v))
        (sigma.obj (D.labelEquiv u)) := by
  rintro ⟨f, hf⟩
  exact ⟨dualMorphism sigma tau D f,
    isIrreducible_dualMorphism sigma tau D hf⟩

/-- Existence of an irreducible arrow is reversed exactly by an aligned
biduality. -/
theorem hasIrreducibleMorphism_dual_iff
    (B : tau.AlignedBiduality sigma) (u v : Kappa) :
    HasIrreducibleMorphism (tau.obj u) (tau.obj v) ↔
      HasIrreducibleMorphism
        (sigma.obj (B.forward.labelEquiv v))
        (sigma.obj (B.forward.labelEquiv u)) := by
  constructor
  · exact hasIrreducibleMorphism_dual sigma tau B.forward u v
  · intro h
    have htarget := hasIrreducibleMorphism_dual tau sigma B.backward
      (B.forward.labelEquiv v) (B.forward.labelEquiv u) h
    simpa only [B.backward_label, Equiv.symm_apply_apply] using htarget

variable [Fintype I] [Fintype Kappa]

/-- Oriented orbit arrows are reversed by the canonical dual-orbit
relabeling. -/
theorem hasOrientedOrbitArrow_dual_iff
    (B : tau.AlignedBiduality sigma)
    (Hsigma : HasAcyclicNonzeroNonisomorphisms sigma)
    (Htau : HasAcyclicNonzeroNonisomorphisms tau)
    (Tsigma : sigma.FiniteARTranslationData)
    (Ttau : tau.FiniteARTranslationData)
    (a b : ProjectiveLabel tau) :
    HasOrientedOrbitArrow tau Htau Ttau a b ↔
      HasOrientedOrbitArrow sigma Hsigma Tsigma
        (dualOrbitLabelEquiv sigma tau B Hsigma Tsigma b)
        (dualOrbitLabelEquiv sigma tau B Hsigma Tsigma a) := by
  let e := dualOrbitLabelEquiv sigma tau B Hsigma Tsigma
  let d := B.forward.labelEquiv
  constructor
  · rintro ⟨u, v, huv, hu, hv⟩
    refine ⟨d v, d u,
      (hasIrreducibleMorphism_dual_iff sigma tau B u v).1 huv, ?_, ?_⟩
    · exact
        (dualOrbitLabelEquiv_arOrbitLabel_of_alignedBiduality
          sigma tau B Hsigma Htau Tsigma Ttau v).symm.trans
          (congrArg e hv)
    · exact
        (dualOrbitLabelEquiv_arOrbitLabel_of_alignedBiduality
          sigma tau B Hsigma Htau Tsigma Ttau u).symm.trans
          (congrArg e hu)
  · rintro ⟨x, y, hxy, hx, hy⟩
    let u : Kappa := d.symm y
    let v : Kappa := d.symm x
    have huv : HasIrreducibleMorphism (tau.obj u) (tau.obj v) := by
      apply (hasIrreducibleMorphism_dual_iff sigma tau B u v).2
      simpa only [u, v, d, Equiv.apply_symm_apply] using hxy
    refine ⟨u, v, huv, ?_, ?_⟩
    · apply e.injective
      rw [dualOrbitLabelEquiv_arOrbitLabel_of_alignedBiduality
        sigma tau B Hsigma Htau Tsigma Ttau u]
      simpa only [u, d, Equiv.apply_symm_apply] using hy
    · apply e.injective
      rw [dualOrbitLabelEquiv_arOrbitLabel_of_alignedBiduality
        sigma tau B Hsigma Htau Tsigma Ttau v]
      simpa only [v, d, Equiv.apply_symm_apply] using hx

/-- Pulling the source orbit graph back along the canonical dual-orbit
equivalence gives the native target orbit graph literally. -/
theorem orbitGraph_comap_dualOrbitLabelEquiv
    (B : tau.AlignedBiduality sigma)
    (Hsigma : HasAcyclicNonzeroNonisomorphisms sigma)
    (Htau : HasAcyclicNonzeroNonisomorphisms tau)
    (Tsigma : sigma.FiniteARTranslationData)
    (Ttau : tau.FiniteARTranslationData) :
    (orbitGraph sigma Hsigma Tsigma).comap
        (dualOrbitLabelEquiv sigma tau B Hsigma Tsigma) =
      orbitGraph tau Htau Ttau := by
  ext a b
  change
    (HasOrientedOrbitArrow sigma Hsigma Tsigma
          (dualOrbitLabelEquiv sigma tau B Hsigma Tsigma a)
          (dualOrbitLabelEquiv sigma tau B Hsigma Tsigma b) ∨
        HasOrientedOrbitArrow sigma Hsigma Tsigma
          (dualOrbitLabelEquiv sigma tau B Hsigma Tsigma b)
          (dualOrbitLabelEquiv sigma tau B Hsigma Tsigma a)) ↔
      (HasOrientedOrbitArrow tau Htau Ttau a b ∨
        HasOrientedOrbitArrow tau Htau Ttau b a)
  rw [← hasOrientedOrbitArrow_dual_iff sigma tau B Hsigma Htau
      Tsigma Ttau b a,
    ← hasOrientedOrbitArrow_dual_iff sigma tau B Hsigma Htau
      Tsigma Ttau a b]
  tauto

/-- Equivalently, mapping the target orbit graph forward along the
dual-orbit equivalence gives the source orbit graph. -/
theorem orbitGraph_map_dualOrbitLabelEquiv
    (B : tau.AlignedBiduality sigma)
    (Hsigma : HasAcyclicNonzeroNonisomorphisms sigma)
    (Htau : HasAcyclicNonzeroNonisomorphisms tau)
    (Tsigma : sigma.FiniteARTranslationData)
    (Ttau : tau.FiniteARTranslationData) :
    (orbitGraph tau Htau Ttau).map
        (dualOrbitLabelEquiv sigma tau B Hsigma Tsigma).toEmbedding =
      orbitGraph sigma Hsigma Tsigma := by
  rw [← orbitGraph_comap_dualOrbitLabelEquiv sigma tau B Hsigma Htau
    Tsigma Ttau]
  ext a b
  let e := dualOrbitLabelEquiv sigma tau B Hsigma Tsigma
  rw [SimpleGraph.map_adj e.toEmbedding]
  constructor
  · rintro ⟨x, y, hxy, hxa, hyb⟩
    change (orbitGraph sigma Hsigma Tsigma).Adj (e x) (e y) at hxy
    change e x = a at hxa
    change e y = b at hyb
    rw [hxa, hyb] at hxy
    exact hxy
  · intro hab
    refine ⟨e.symm a, e.symm b, ?_, by simp [e], by simp [e]⟩
    change (orbitGraph sigma Hsigma Tsigma).Adj
      (e (e.symm a)) (e (e.symm b))
    simpa using hab

/-! ## Simply-laced Coxeter transport along a graph relabeling -/

universe uA uB

variable {A : Type uA} {BLabel : Type uB}

/-- Reindexing the simply-laced Coxeter matrix is the same operation as
mapping the underlying graph along the indexing equivalence. -/
theorem matrix_reindex_equiv
    (G : SimpleGraph A) (e : A ≃ BLabel) :
    (matrix G).reindex e = matrix (G.map e.toEmbedding) := by
  ext i j
  rw [CoxeterMatrix.reindex_apply]
  by_cases hij : i = j
  · subst j
    simp
  · have hpre : e.symm i ≠ e.symm j := by
      exact fun h ↦ hij (e.symm.injective h)
    by_cases hadj : G.Adj (e.symm i) (e.symm j)
    · rw [matrix_apply_of_adj G hadj]
      symm
      apply matrix_apply_of_adj
      rw [SimpleGraph.map_adj e.toEmbedding]
      exact ⟨e.symm i, e.symm j, hadj, by simp, by simp⟩
    · rw [matrix_apply_of_ne_of_not_adj G hpre hadj]
      symm
      apply matrix_apply_of_ne_of_not_adj
      · exact hij
      · rw [SimpleGraph.map_adj e.toEmbedding]
        rintro ⟨a, b, hab, ha, hb⟩
        apply hadj
        have hae : a = e.symm i := by
          apply e.injective
          simpa only [ha, Equiv.apply_symm_apply]
        have hbe : b = e.symm j := by
          apply e.injective
          simpa only [hb, Equiv.apply_symm_apply]
        simpa only [hae, hbe] using hab

/-- The target orbit Coxeter matrix, reindexed by dual orbit labels, is
literally the source orbit Coxeter matrix. -/
theorem orbitCoxeterMatrix_reindex_dualOrbitLabelEquiv
    (B : tau.AlignedBiduality sigma)
    (Hsigma : HasAcyclicNonzeroNonisomorphisms sigma)
    (Htau : HasAcyclicNonzeroNonisomorphisms tau)
    (Tsigma : sigma.FiniteARTranslationData)
    (Ttau : tau.FiniteARTranslationData) :
    (matrix (orbitGraph tau Htau Ttau)).reindex
        (dualOrbitLabelEquiv sigma tau B Hsigma Tsigma) =
      matrix (orbitGraph sigma Hsigma Tsigma) := by
  rw [matrix_reindex_equiv]
  exact congrArg matrix
    (orbitGraph_map_dualOrbitLabelEquiv sigma tau B Hsigma Htau
      Tsigma Ttau)

/-- Mapping a graph and every letter of a word along an equivalence
preserves and reflects reducedness in the simply-laced Coxeter group. -/
theorem isReduced_map_equiv_iff
    (G : SimpleGraph A) (e : A ≃ BLabel) (Q : List A) :
    IsReduced (G.map e.toEmbedding) (Q.map e) ↔ IsReduced G Q := by
  constructor
  · intro h
    have hpull := isReduced_pullback_of_map_isReduced
      (G.map e.toEmbedding) e Q h
    have hGraph : pullbackGraph (G.map e.toEmbedding) e = G := by
      ext a b
      exact SimpleGraph.map_adj_apply
    rw [hGraph] at hpull
    exact hpull
  · intro h
    have hMappedBack : IsReduced G ((Q.map e).map e.symm) := by
      simpa [List.map_map] using h
    have hpull := isReduced_pullback_of_map_isReduced
      G e.symm (Q.map e) hMappedBack
    have hGraph : pullbackGraph G e.symm = G.map e.toEmbedding := by
      ext a b
      rw [SimpleGraph.map_adj e.toEmbedding]
      constructor
      · intro hab
        exact ⟨e.symm a, e.symm b, hab, by simp, by simp⟩
      · rintro ⟨x, y, hxy, hxa, hyb⟩
        have hx : x = e.symm a := by
          apply e.injective
          simpa only [hxa, Equiv.apply_symm_apply]
        have hy : y = e.symm b := by
          apply e.injective
          simpa only [hyb, Equiv.apply_symm_apply]
        simpa only [pullbackGraph_adj, hx, hy] using hxy
    rw [hGraph] at hpull
    exact hpull

/-- Reducedness of a target orbit word is equivalent to reducedness after
relabeling its letters into the source orbit graph. -/
theorem isReduced_dualOrbitLabelEquiv_iff
    (B : tau.AlignedBiduality sigma)
    (Hsigma : HasAcyclicNonzeroNonisomorphisms sigma)
    (Htau : HasAcyclicNonzeroNonisomorphisms tau)
    (Tsigma : sigma.FiniteARTranslationData)
    (Ttau : tau.FiniteARTranslationData)
    (Q : List (ProjectiveLabel tau)) :
    IsReduced (orbitGraph sigma Hsigma Tsigma)
        (Q.map (dualOrbitLabelEquiv sigma tau B Hsigma Tsigma)) ↔
      IsReduced (orbitGraph tau Htau Ttau) Q := by
  rw [← orbitGraph_map_dualOrbitLabelEquiv sigma tau B Hsigma Htau
    Tsigma Ttau]
  exact isReduced_map_equiv_iff (orbitGraph tau Htau Ttau)
    (dualOrbitLabelEquiv sigma tau B Hsigma Tsigma) Q

/-! ## Position and local-subword transport -/

/-- The value-preserving identification between positions in a mapped list
and positions in the original list. -/
def mapIndexEquiv (Q : List A) (e : A ≃ BLabel) :
    Fin (Q.map e).length ≃ Fin Q.length :=
  finCongr (by simp)

@[simp]
theorem mapIndexEquiv_apply_val
    (Q : List A) (e : A ≃ BLabel)
    (p : Fin (Q.map e).length) :
    (mapIndexEquiv Q e p).val = p.val :=
  rfl

@[simp]
theorem mapIndexEquiv_symm_apply_val
    (Q : List A) (e : A ≃ BLabel)
    (p : Fin Q.length) :
    ((mapIndexEquiv Q e).symm p).val = p.val :=
  rfl

theorem mapIndexEquiv_le_iff
    (Q : List A) (e : A ≃ BLabel)
    (p q : Fin (Q.map e).length) :
    mapIndexEquiv Q e p ≤ mapIndexEquiv Q e q ↔ p ≤ q := by
  rfl

theorem mapIndexEquiv_lt_iff
    (Q : List A) (e : A ≃ BLabel)
    (p q : Fin (Q.map e).length) :
    mapIndexEquiv Q e p < mapIndexEquiv Q e q ↔ p < q := by
  rfl

/-- A set of positions in a mapped list, transported back to the original
list. -/
def originalPositions
    (Q : List A) (e : A ≃ BLabel)
    (positions : Finset (Fin (Q.map e).length)) :
    Finset (Fin Q.length) :=
  positions.map (mapIndexEquiv Q e).toEmbedding

@[simp]
theorem mem_originalPositions_iff
    (Q : List A) (e : A ≃ BLabel)
    (positions : Finset (Fin (Q.map e).length))
    (p : Fin (Q.map e).length) :
    mapIndexEquiv Q e p ∈ originalPositions Q e positions ↔
      p ∈ positions := by
  simp [originalPositions]

/-- Sorting transported positions is the same as transporting the sorted
position list. -/
theorem sort_originalPositions
    (Q : List A) (e : A ≃ BLabel)
    (positions : Finset (Fin (Q.map e).length)) :
    (originalPositions Q e positions).sort (· ≤ ·) =
      (positions.sort (· ≤ ·)).map (mapIndexEquiv Q e) := by
  unfold originalPositions
  symm
  simpa only [Equiv.coe_toEmbedding] using
    (Finset.map_sort
      (f := (mapIndexEquiv Q e).toEmbedding)
      (s := positions) (r := (· ≤ ·)) (r' := (· ≤ ·))
      (fun a _ b _ ↦ mapIndexEquiv_le_iff Q e a b))

/-- Selecting from a mapped word agrees with selecting the corresponding
original positions and then mapping the selected letters. -/
theorem subwordAt_map_equiv
    (Q : List A) (e : A ≃ BLabel)
    (positions : Finset (Fin (Q.map e).length)) :
    subwordAt (Q.map e) positions =
      (subwordAt Q (originalPositions Q e positions)).map e := by
  simp only [subwordAt, sort_originalPositions, List.map_map]
  apply List.map_congr_left
  intro p hp
  simp [mapIndexEquiv]

/-- Row-restricted position sets commute with the value-preserving position
identification for a mapped list. -/
theorem originalPositions_localPositions
    (Q : List A) (e : A ≃ BLabel)
    (positions : Finset (Fin (Q.map e).length))
    (a : Fin (Q.map e).length) :
    originalPositions Q e
        (SortingExchange.localPositions positions a) =
      SortingExchange.localPositions (originalPositions Q e positions)
        (mapIndexEquiv Q e a) := by
  ext x
  obtain ⟨p, rfl⟩ := (mapIndexEquiv Q e).surjective x
  simp only [SortingExchange.localPositions,
    mem_originalPositions_iff, mem_rowRestrictedOmissions_iff]
  rw [mapIndexEquiv_lt_iff]
  simp

/-- Every local subword is reduced before relabeling exactly when every
local subword is reduced after relabeling the graph and word. -/
theorem areAllLocalSubwordsReduced_map_equiv_iff
    (G : SimpleGraph A) (e : A ≃ BLabel) (Q : List A)
    (positions : Finset (Fin (Q.map e).length)) :
    SortingExchange.AreAllLocalSubwordsReduced
        (system (G.map e.toEmbedding)) (Q.map e) positions ↔
      SortingExchange.AreAllLocalSubwordsReduced
        (system G) Q (originalPositions Q e positions) := by
  constructor
  · intro h a
    let aMapped : Fin (Q.map e).length := (mapIndexEquiv Q e).symm a
    have hMapped := h aMapped
    rw [subwordAt_map_equiv Q e
      (SortingExchange.localPositions positions aMapped)] at hMapped
    have hOriginal :=
      (isReduced_map_equiv_iff G e
        (subwordAt Q (originalPositions Q e
          (SortingExchange.localPositions positions aMapped)))).1 hMapped
    rw [originalPositions_localPositions Q e positions aMapped] at hOriginal
    change (system G).IsReduced _ at hOriginal
    simpa only [aMapped, Equiv.apply_symm_apply] using hOriginal
  · intro h a
    have hOriginal := h (mapIndexEquiv Q e a)
    rw [← originalPositions_localPositions Q e positions a] at hOriginal
    have hMapped :=
      (isReduced_map_equiv_iff G e
        (subwordAt Q (originalPositions Q e
          (SortingExchange.localPositions positions a)))).2 hOriginal
    rwa [← subwordAt_map_equiv Q e
      (SortingExchange.localPositions positions a)] at hMapped

/-- Orbit-local reducedness transports exactly from the native target graph
to the source graph after dual-orbit relabeling. -/
theorem areAllLocalSubwordsReduced_dualOrbitLabelEquiv_iff
    (B : tau.AlignedBiduality sigma)
    (Hsigma : HasAcyclicNonzeroNonisomorphisms sigma)
    (Htau : HasAcyclicNonzeroNonisomorphisms tau)
    (Tsigma : sigma.FiniteARTranslationData)
    (Ttau : tau.FiniteARTranslationData)
    (Q : List (ProjectiveLabel tau))
    (positions : Finset (Fin
      (Q.map (dualOrbitLabelEquiv sigma tau B Hsigma Tsigma)).length)) :
    SortingExchange.AreAllLocalSubwordsReduced
        (system (orbitGraph sigma Hsigma Tsigma))
        (Q.map (dualOrbitLabelEquiv sigma tau B Hsigma Tsigma))
        positions ↔
      SortingExchange.AreAllLocalSubwordsReduced
        (system (orbitGraph tau Htau Ttau)) Q
        (originalPositions Q
          (dualOrbitLabelEquiv sigma tau B Hsigma Tsigma) positions) := by
  rw [← orbitGraph_map_dualOrbitLabelEquiv sigma tau B Hsigma Htau
    Tsigma Ttau]
  exact areAllLocalSubwordsReduced_map_equiv_iff
    (orbitGraph tau Htau Ttau)
    (dualOrbitLabelEquiv sigma tau B Hsigma Tsigma) Q positions

/-- Omitted labels are unchanged when mapped-word positions are transported
back along the value-preserving index equivalence. -/
theorem omittedLabelsFor_map_equiv
    {J : Type*}
    (Q : List A) (e : A ≃ BLabel)
    (position : Fin Q.length ≃ J)
    (positions : Finset (Fin (Q.map e).length)) :
    omittedLabelsFor ((mapIndexEquiv Q e).trans position) positions =
      omittedLabelsFor position (originalPositions Q e positions) := by
  ext j
  obtain ⟨p, rfl⟩ := ((mapIndexEquiv Q e).trans position).surjective j
  change
    (((mapIndexEquiv Q e).trans position) p ∈
        omittedLabelsFor ((mapIndexEquiv Q e).trans position) positions) ↔
      position (mapIndexEquiv Q e p) ∈
        omittedLabelsFor position (originalPositions Q e positions)
  rw [mem_omittedLabelsFor_iff, mem_omittedLabelsFor_iff,
    mem_originalPositions_iff]

/-- A local sorting/closure correspondence transports from a graph word to
the equivalently relabeled graph word. -/
theorem hasLocalClosureCorrespondence_map_equiv
    {R' : Type*} [Ring R'] [IsNoetherianRing R']
    {J : Type*} [Fintype J]
    (rho : IndecomposableSkeleton.{_, _, _} R' J)
    (G : SimpleGraph A) (e : A ≃ BLabel) (Q : List A)
    (position : Fin Q.length ≃ J)
    (hSort : HasLocalClosureCorrespondence rho G Q position) :
    HasLocalClosureCorrespondence rho (G.map e.toEmbedding) (Q.map e)
      ((mapIndexEquiv Q e).trans position) := by
  intro positions
  rw [areAllLocalSubwordsReduced_map_equiv_iff G e Q positions,
    omittedLabelsFor_map_equiv Q e position positions]
  exact hSort (originalPositions Q e positions)

/-- Smallest bridge consumed by the final opposite-profile assembly: native
target directed sorting over its own orbit graph becomes the same closure
correspondence for the dual-relabelled word over the source orbit graph. -/
theorem hasLocalClosureCorrespondence_dualOrbitLabelEquiv
    (B : tau.AlignedBiduality sigma)
    (Hsigma : HasAcyclicNonzeroNonisomorphisms sigma)
    (Htau : HasAcyclicNonzeroNonisomorphisms tau)
    (Tsigma : sigma.FiniteARTranslationData)
    (Ttau : tau.FiniteARTranslationData)
    (Q : List (ProjectiveLabel tau))
    (position : Fin Q.length ≃ Kappa)
    (hSort : HasLocalClosureCorrespondence tau
      (orbitGraph tau Htau Ttau) Q position) :
    HasLocalClosureCorrespondence tau
      (orbitGraph sigma Hsigma Tsigma)
      (Q.map (dualOrbitLabelEquiv sigma tau B Hsigma Tsigma))
      ((mapIndexEquiv Q
        (dualOrbitLabelEquiv sigma tau B Hsigma Tsigma)).trans position) := by
  rw [← orbitGraph_map_dualOrbitLabelEquiv sigma tau B Hsigma Htau
    Tsigma Ttau]
  exact hasLocalClosureCorrespondence_map_equiv tau
    (orbitGraph tau Htau Ttau)
    (dualOrbitLabelEquiv sigma tau B Hsigma Tsigma) Q position hSort

/-! ## Direct consumption of explicit-order directed sorting -/

/-- Uniform finite mesh exactness turns the explicit-order
`directedSortingFor` theorem into the precise local closure correspondence
consumed by the positioned quotient-profile adapter. -/
theorem hasLocalClosureCorrespondence_wordFor
    {KField : Type uS} [Field KField] [IsAlgClosed KField]
    [Algebra KField S] [FiniteDimensional KField S]
    (Htau : HasAcyclicNonzeroNonisomorphisms tau)
    (Ttau : tau.FiniteARTranslationData)
    (E : DirectedOrderChoice tau)
    (hMeshExactness :
      ∀ (D : Finset (Fin (wordFor tau Htau Ttau E).length))
        (a : Fin (wordFor tau Htau Ttau E).length),
        PositiveRightAdditiveForcesMeshInverseNonnegative
          (segmentGraph (orbitGraph tau Htau Ttau)
            (wordFor tau Htau Ttau E)
            (rowRestrictedOmissions D a))
          (segmentWord (wordFor tau Htau Ttau E)
            (rowRestrictedOmissions D a))) :
    HasLocalClosureCorrespondence tau
      (orbitGraph tau Htau Ttau) (wordFor tau Htau Ttau E)
      (positionEquivFor tau Htau Ttau E) := by
  letI : Finite (ProjectiveLabel tau) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype (ProjectiveLabel tau) := Fintype.ofFinite _
  intro D
  have hThree := directedSortingFor (K := KField) (R := S)
    tau Htau Ttau E D (hMeshExactness D)
  rw [← SortingExchange.leftmostReducedSubwordFor_iff_allLocal_simpleGraph]
  simpa only [omittedLabelsFor, omittedLabelFinsetFor] using
    hThree.1.trans hThree.2

/-- Native target explicit-order directed sorting, followed by the abstract
orbit/Coxeter relabeling bridge, produces exactly the source-graph local
closure correspondence required by the final opposite-profile assembly. -/
theorem directedSortingFor_dualRelabelledLocalClosure
    {KField : Type uS} [Field KField] [IsAlgClosed KField]
    [Algebra KField S] [FiniteDimensional KField S]
    (B : tau.AlignedBiduality sigma)
    (Hsigma : HasAcyclicNonzeroNonisomorphisms sigma)
    (Htau : HasAcyclicNonzeroNonisomorphisms tau)
    (Tsigma : sigma.FiniteARTranslationData)
    (Ttau : tau.FiniteARTranslationData)
    (E : DirectedOrderChoice tau)
    (hMeshExactness :
      ∀ (D : Finset (Fin (wordFor tau Htau Ttau E).length))
        (a : Fin (wordFor tau Htau Ttau E).length),
        PositiveRightAdditiveForcesMeshInverseNonnegative
          (segmentGraph (orbitGraph tau Htau Ttau)
            (wordFor tau Htau Ttau E)
            (rowRestrictedOmissions D a))
          (segmentWord (wordFor tau Htau Ttau E)
            (rowRestrictedOmissions D a))) :
    HasLocalClosureCorrespondence tau
      (orbitGraph sigma Hsigma Tsigma)
      ((wordFor tau Htau Ttau E).map
        (dualOrbitLabelEquiv sigma tau B Hsigma Tsigma))
      ((mapIndexEquiv (wordFor tau Htau Ttau E)
        (dualOrbitLabelEquiv sigma tau B Hsigma Tsigma)).trans
          (positionEquivFor tau Htau Ttau E)) :=
  hasLocalClosureCorrespondence_dualOrbitLabelEquiv
    sigma tau B Hsigma Htau Tsigma Ttau
    (wordFor tau Htau Ttau E) (positionEquivFor tau Htau Ttau E)
    (hasLocalClosureCorrespondence_wordFor (KField := KField)
      tau Htau Ttau E hMeshExactness)

end QuotientSubmoduleEquidistribution.RepresentationDirected.OrbitGraphDuality
