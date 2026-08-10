import QuotientSubmoduleEquidistribution.RepresentationTheory.GabrielArrowBridge
import QuotientSubmoduleEquidistribution.RepresentationTheory.LengthThreeModules
import QuotientSubmoduleEquidistribution.Combinatorics.BottomThreeAdapter

/-!
# Non-uniserial quotient-side shapes at level three

This file develops the four non-uniserial families in the manuscript's
level-three classification.  It separates support
combinatorics and individual quotient closure from the genuinely collective
finite-biproduct issue.
-/

noncomputable section

open Set
open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

universe u v w

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-! ## Adding simple generators -/

/-- The trace of a support consisting of simple representatives is a
semisimple submodule of every target. -/
theorem trace_isSemisimple_of_forall_simple
    {T : Set ι} (hT : ∀ i ∈ T, Simple (σ.obj i))
    (X : FGModuleCat.{w} R) :
    IsSemisimpleModule R (σ.trace T X) := by
  unfold trace
  have hp : ∀ f : σ.SelectedMapTo T X,
      IsSemisimpleModule R (LinearMap.range f.map.hom.hom) := by
    intro f
    letI (t : f.index) : Simple (σ.obj (f.label t)) :=
      hT (f.label t) (f.mem t)
    letI (t : f.index) : IsSimpleModule R (σ.obj (f.label t)) :=
      (simple_iff_isSimpleModule_fg _).mp inferInstance
    letI : IsSemisimpleModule R
        (∀ t : f.index, σ.obj (f.label t)) :=
      inferInstance
    let e :
        σ.sumOver f.index f.label ≅
          FGModuleCat.of R (∀ t : f.index, σ.obj (f.label t)) :=
      biproductIsoPiFG _
    letI : IsSemisimpleModule R (σ.sumOver f.index f.label) :=
      (LinearEquiv.isSemisimpleModule_iff
        (FGModuleCat.isoToLinearEquiv e)).mpr inferInstance
    exact
      IsSemisimpleModule.of_surjective
        f.map.hom.hom.rangeRestrict
        f.map.hom.hom.surjective_rangeRestrict
  let p : σ.SelectedMapTo T X → Submodule R X :=
    fun f ↦ LinearMap.range f.map.hom.hom
  have hsemisimple :
      IsSemisimpleModule R ↥(⨆ f ∈ (Set.univ : Set (σ.SelectedMapTo T X)), p f) :=
    isSemisimpleModule_biSup_of_isSemisimpleModule_submodule
      (s := Set.univ) (p := p) (fun f _ ↦ hp f)
  have heq :
      (⨆ f ∈ (Set.univ : Set (σ.SelectedMapTo T X)), p f) =
        ⨆ f, p f := by
    simp
  rw [← heq]
  exact hsemisimple

omit [IsNoetherianRing R] in
/-- In an indecomposable module, a semisimple submodule which together with
an arbitrary submodule spans the whole module forces one of the two
submodules to be the whole module. -/
theorem eq_top_or_eq_top_of_sup_eq_top_of_semisimple
    {M : Type w} [AddCommGroup M] [Module R M]
    (hM : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R M)
    (N U : Submodule R M)
    (hU : IsSemisimpleModule R U)
    (hsup : N ⊔ U = ⊤) :
    N = ⊤ ∨ U = ⊤ := by
  letI : IsSemisimpleModule R U := hU
  let W : Submodule R U := N.comap U.subtype
  obtain ⟨V, hWV⟩ := exists_isCompl W
  let V' : Submodule R M := V.map U.subtype
  have hV'U : V' ≤ U := Submodule.map_subtype_le U V
  have hdisjoint : N ⊓ V' = ⊥ := by
    ext x
    constructor
    · rintro ⟨hxN, hxV⟩
      rcases hxV with ⟨y, hyV, rfl⟩
      have hyW : y ∈ W := by
        change (y : M) ∈ N
        exact hxN
      have hyBot : y ∈ (⊥ : Submodule R U) := by
        rw [← hWV.inf_eq_bot]
        exact ⟨hyW, hyV⟩
      have hyZero : y = 0 := by
        simpa using hyBot
      simp [hyZero]
    · intro hx
      have hxZero : x = 0 := by
        simpa using hx
      subst x
      simp
  have hUle : U ≤ N ⊔ V' := by
    intro x hxU
    let xU : U := ⟨x, hxU⟩
    have hxWV : xU ∈ W ⊔ V := by
      rw [hWV.sup_eq_top]
      trivial
    rcases Submodule.mem_sup.mp hxWV with
      ⟨y, hyW, z, hzV, hyz⟩
    have hyN : (y : M) ∈ N := by
      exact hyW
    have hzV' : (z : M) ∈ V' := by
      exact ⟨z, hzV, rfl⟩
    apply Submodule.mem_sup.mpr
    refine ⟨(y : M), hyN, (z : M), hzV', ?_⟩
    exact congrArg Subtype.val hyz
  have hsup' : N ⊔ V' = ⊤ := by
    apply top_unique
    rw [← hsup]
    exact sup_le le_sup_left hUle
  have hcompl : IsCompl N V' :=
    IsCompl.of_eq hdisjoint hsup'
  rcases hM.eq_bot_or_eq_bot hcompl with hN | hV
  · right
    have hV'top : V' = ⊤ := by
      simpa [hN] using hsup'
    apply top_unique
    simpa [hV'top] using hV'U
  · left
    simpa [hV] using hsup'

/-- Adjoining any collection of simple representatives to a quotient-closed
support preserves collective quotient closedness.  This is the missing
collective argument for the manuscript's "one edge plus an extra vertex"
family: the trace of the added simples is semisimple, and an indecomposable
target cannot be the nontrivial sum of the old trace and a semisimple
complement. -/
theorem qClosure_isClosed_union_of_forall_simple
    {S T : Set ι}
    (hS : σ.qClosure.IsClosed S)
    (hT : ∀ i ∈ T, Simple (σ.obj i)) :
    σ.qClosure.IsClosed (S ∪ T) := by
  rw [σ.qClosure.isClosed_iff]
  apply Set.Subset.antisymm
  · intro j hj
    have htrace :
        σ.trace (S ∪ T) (σ.obj j) = ⊤ :=
      (σ.mem_qClosure_iff_trace_eq_top (S ∪ T) j).mp hj
    rw [σ.trace_union] at htrace
    have hsemisimple :
        IsSemisimpleModule R (σ.trace T (σ.obj j)) :=
      σ.trace_isSemisimple_of_forall_simple hT (σ.obj j)
    rcases
        eq_top_or_eq_top_of_sup_eq_top_of_semisimple (R := R)
          (σ.indecomposable j)
          (σ.trace S (σ.obj j))
          (σ.trace T (σ.obj j))
          hsemisimple htrace with hOld | hSimple
    · left
      rw [← hS.closure_eq]
      exact
        (σ.mem_qClosure_iff_trace_eq_top S j).mpr hOld
    · right
      let hTclosed : σ.qClosure.IsClosed T :=
        σ.qClosure_isClosed_of_forall_simple hT
      rw [← hTclosed.closure_eq]
      exact
        (σ.mem_qClosure_iff_trace_eq_top T j).mpr hSimple
  · exact σ.subset_qSet (S ∪ T)

/-- Adjoining simple representatives after taking quotient closure creates
no further nonsimple objects: closure commutes with this particular union. -/
theorem qClosure_union_eq_closure_union_of_forall_simple
    {S T : Set ι} (hT : ∀ i ∈ T, Simple (σ.obj i)) :
    σ.qClosure (S ∪ T) = σ.qClosure S ∪ T := by
  apply Set.Subset.antisymm
  · apply σ.qClosure.closure_min
    · exact Set.union_subset
        (fun i hi ↦ Set.mem_union_left T (σ.subset_qSet S hi))
        Set.subset_union_right
    · exact σ.qClosure_isClosed_union_of_forall_simple
        (σ.qClosure.isClosed_closure S) hT
  · apply Set.union_subset
    · exact σ.qClosure.monotone Set.subset_union_left
    · exact Set.subset_union_right.trans
        (σ.qClosure.le_closure (S ∪ T))

/-! ## Reusable collective-closure interface -/

/-- Every indecomposable quotient of a single selected representative stays
in the selected support. -/
def IndividuallyQuotientClosed (S : Set ι) : Prop :=
  ∀ {i j : ι}, i ∈ S →
    ∀ (f : σ.obj i ⟶ σ.obj j), Epi f → j ∈ S

/-- Every jointly epic presentation from a support has an epic component. -/
def FacPresentationsHaveEpiComponent (S : Set ι) : Prop :=
  ∀ {j : ι} (P : σ.FacPresentation S (σ.obj j)),
    ∃ t : P.index,
      Epi
        (biproduct.ι
            (fun a : P.index ↦ σ.obj (P.label a)) t ≫
          P.map)

/-- Individual quotient closure plus the epic-component property implies
the genuinely collective closure condition. -/
theorem qClosure_isClosed_of_individual_of_epiComponent
    {S : Set ι}
    (hindividual : σ.IndividuallyQuotientClosed S)
    (hcomponent : σ.FacPresentationsHaveEpiComponent S) :
    σ.qClosure.IsClosed S := by
  rw [σ.qClosure.isClosed_iff]
  apply Set.Subset.antisymm
  · intro j hj
    obtain ⟨P⟩ := hj
    obtain ⟨t, ht⟩ := hcomponent P
    exact hindividual (P.mem t)
      (biproduct.ι
          (fun a : P.index ↦ σ.obj (P.label a)) t ≫
        P.map) ht
  · exact σ.subset_qSet S

/-- An epimorphism from a simple chosen representative to another chosen
indecomposable is an isomorphism, hence preserves its skeleton index. -/
theorem index_eq_of_epi_from_simple
    {i j : ι} (hi : Simple (σ.obj i))
    (f : σ.obj i ⟶ σ.obj j) [Epi f] :
    j = i := by
  have hle := σ.compositionLength_le_of_epi f
  have hiLength : σ.compositionLength i = 1 :=
    (σ.compositionLength_eq_one_iff_simple i).2 hi
  have hjPos := σ.compositionLength_pos j
  have hjLength : σ.compositionLength j = 1 := by
    omega
  haveI : IsIso f :=
    σ.isIso_of_epi_of_compositionLength_eq f
      (hiLength.trans hjLength.symm)
  exact (σ.eq_of_iso ⟨asIso f⟩).symm

/-! ## Family 1: three simple representatives -/

/-- Unordered triples of distinct simple skeleton indices. -/
def SimpleTriple :=
  {P : Finset σ.SimpleIndex // P.card = 3}

/-- The underlying three-simple support in the full skeleton. -/
def simpleTripleSupport (P : σ.SimpleTriple) : Set ι :=
  σ.simpleIndexEmbedding '' (P.1 : Set σ.SimpleIndex)

@[simp]
theorem ncard_simpleTripleSupport (P : σ.SimpleTriple) :
    (σ.simpleTripleSupport P).ncard = 3 := by
  rw [simpleTripleSupport,
    Set.ncard_image_of_injective _ σ.simpleIndexEmbedding.injective,
    Set.ncard_coe_finset, P.2]

theorem simple_of_mem_simpleTripleSupport
    (P : σ.SimpleTriple) {i : ι}
    (hi : i ∈ σ.simpleTripleSupport P) :
    Simple (σ.obj i) := by
  rcases hi with ⟨s, -, rfl⟩
  exact s.2

theorem simpleTripleSupport_injective :
    Function.Injective σ.simpleTripleSupport := by
  intro P Q hPQ
  apply Subtype.ext
  apply Finset.ext
  intro s
  constructor
  · intro hs
    have hsSupport :
        σ.simpleIndexEmbedding s ∈
          σ.simpleTripleSupport P :=
      ⟨s, hs, rfl⟩
    rw [hPQ] at hsSupport
    rcases hsSupport with ⟨t, ht, hts⟩
    have hts' : t = s :=
      σ.simpleIndexEmbedding.injective hts
    simpa [hts'] using ht
  · intro hs
    have hsSupport :
        σ.simpleIndexEmbedding s ∈
          σ.simpleTripleSupport Q :=
      ⟨s, hs, rfl⟩
    rw [← hPQ] at hsSupport
    rcases hsSupport with ⟨t, ht, hts⟩
    have hts' : t = s :=
      σ.simpleIndexEmbedding.injective hts
    simpa [hts'] using ht

/-- The unconditional realization of the first family as an actual closed
three-element support. -/
def simpleTripleToClosedLevelThree
    (P : σ.SimpleTriple) :
    QuotientSubmoduleEquidistribution.BottomLevels.BottomThreeAdapter.ClosedLevelThree
      σ.qClosure :=
  ⟨⟨σ.simpleTripleSupport P,
      σ.qClosure_isClosed_of_forall_simple
        (fun _ hi ↦ σ.simple_of_mem_simpleTripleSupport P hi)⟩,
    σ.ncard_simpleTripleSupport P⟩

theorem simpleTripleToClosedLevelThree_injective :
    Function.Injective σ.simpleTripleToClosedLevelThree := by
  intro P Q hPQ
  apply σ.simpleTripleSupport_injective
  exact congrArg (fun C ↦ (C.1.1 : Set ι)) hPQ

/-! ## Family 2: one length-two object and an extra simple -/

/-- A length-two index and a simple index different from its chosen source.
For the Gabriel realization, `source` is the simple top. -/
def EdgeExtraSimple
    (source : σ.LengthTwoIndex → σ.SimpleIndex) :=
  Σ e : σ.LengthTwoIndex,
    {s : σ.SimpleIndex // s ≠ source e}

/-- The three indices in the edge-plus-extra-simple family. -/
def edgeExtraSimpleSupport
    (source : σ.LengthTwoIndex → σ.SimpleIndex)
    (p : σ.EdgeExtraSimple source) : Set ι :=
  {p.1.1, (source p.1).1, p.2.1.1}

theorem lengthTwoIndex_ne_simpleIndex
    (e : σ.LengthTwoIndex) (s : σ.SimpleIndex) :
    e.1 ≠ s.1 := by
  intro h
  exact σ.lengthTwoIndex_not_simple e (by simpa [h] using s.2)

@[simp]
theorem ncard_edgeExtraSimpleSupport
    (source : σ.LengthTwoIndex → σ.SimpleIndex)
    (p : σ.EdgeExtraSimple source) :
    (σ.edgeExtraSimpleSupport source p).ncard = 3 := by
  have hes : p.1.1 ≠ (source p.1).1 :=
    σ.lengthTwoIndex_ne_simpleIndex p.1 (source p.1)
  have het : p.1.1 ≠ p.2.1.1 :=
    σ.lengthTwoIndex_ne_simpleIndex p.1 p.2.1
  have hst : (source p.1).1 ≠ p.2.1.1 := by
    intro h
    exact p.2.2 (Subtype.ext h.symm)
  simp [edgeExtraSimpleSupport, hes, het, hst]

theorem edgeExtraSimpleSupport_injective
    (source : σ.LengthTwoIndex → σ.SimpleIndex) :
    Function.Injective (σ.edgeExtraSimpleSupport source) := by
  rintro ⟨e, s⟩ ⟨e', s'⟩ hsupport
  have heMem :
      e.1 ∈ σ.edgeExtraSimpleSupport source ⟨e', s'⟩ := by
    rw [← hsupport]
    simp [edgeExtraSimpleSupport]
  have heVal : e.1 = e'.1 := by
    rcases (by
      simpa [edgeExtraSimpleSupport] using heMem) with
      h | h | h
    · exact h
    · exact False.elim
        (σ.lengthTwoIndex_ne_simpleIndex e (source e') h)
    · exact False.elim
        (σ.lengthTwoIndex_ne_simpleIndex e s'.1 h)
  have he : e = e' := Subtype.ext heVal
  subst e'
  have hsMem :
      s.1.1 ∈ σ.edgeExtraSimpleSupport source ⟨e, s'⟩ := by
    rw [← hsupport]
    simp [edgeExtraSimpleSupport]
  have hsVal : s.1.1 = s'.1.1 := by
    rcases (by
      simpa [edgeExtraSimpleSupport] using hsMem) with
      h | h | h
    · exact False.elim
        (σ.lengthTwoIndex_ne_simpleIndex e s.1 h.symm)
    · exact False.elim
        (s.2 (Subtype.ext h))
    · exact h
  have hs : s = s' := Subtype.ext (Subtype.ext hsVal)
  subst s'
  rfl

/-- Once the usual length-two/top pair is collectively closed, adding the
extra simple is unconditionally collectively closed. -/
theorem qClosure_isClosed_edgeExtraSimpleSupport
    (source : σ.LengthTwoIndex → σ.SimpleIndex)
    (hpair : ∀ e : σ.LengthTwoIndex,
      σ.qClosure.IsClosed ({e.1, (source e).1} : Set ι))
    (p : σ.EdgeExtraSimple source) :
    σ.qClosure.IsClosed (σ.edgeExtraSimpleSupport source p) := by
  have hclosed :=
    σ.qClosure_isClosed_union_of_forall_simple (hpair p.1)
      (T := ({p.2.1.1} : Set ι))
      (by
        intro i hi
        have hi' : i = p.2.1.1 := by simpa using hi
        simpa [hi'] using p.2.1.2)
  have heq :
      σ.edgeExtraSimpleSupport source p =
        ({p.1.1, (source p.1).1} : Set ι) ∪ {p.2.1.1} := by
    ext i
    simp [edgeExtraSimpleSupport, or_left_comm, or_comm]
  rw [heq]
  exact hclosed

/-- The injective realization of family 2, conditional only on the already
isolated closed-pair input. -/
def edgeExtraSimpleToClosedLevelThree
    (source : σ.LengthTwoIndex → σ.SimpleIndex)
    (hpair : ∀ e : σ.LengthTwoIndex,
      σ.qClosure.IsClosed ({e.1, (source e).1} : Set ι))
    (p : σ.EdgeExtraSimple source) :
    QuotientSubmoduleEquidistribution.BottomLevels.BottomThreeAdapter.ClosedLevelThree
      σ.qClosure :=
  ⟨⟨σ.edgeExtraSimpleSupport source p,
      σ.qClosure_isClosed_edgeExtraSimpleSupport source hpair p⟩,
    σ.ncard_edgeExtraSimpleSupport source p⟩

theorem edgeExtraSimpleToClosedLevelThree_injective
    (source : σ.LengthTwoIndex → σ.SimpleIndex)
    (hpair : ∀ e : σ.LengthTwoIndex,
      σ.qClosure.IsClosed ({e.1, (source e).1} : Set ι)) :
    Function.Injective
      (σ.edgeExtraSimpleToClosedLevelThree source hpair) := by
  intro p q hpq
  apply σ.edgeExtraSimpleSupport_injective source
  exact congrArg (fun C ↦ (C.1.1 : Set ι)) hpq

/-! ## Family 3: two length-two objects with a common top -/

/-- The length-two indices with a prescribed chosen source. -/
abbrev CommonSourceFiber
    (source : σ.LengthTwoIndex → σ.SimpleIndex)
    (s : σ.SimpleIndex) :=
  {e : σ.LengthTwoIndex // source e = s}

/-- An unordered pair of distinct length-two indices with one common chosen
simple source. -/
def CommonSourcePair
    (source : σ.LengthTwoIndex → σ.SimpleIndex) :=
  Σ s : σ.SimpleIndex,
    {P : Finset (σ.CommonSourceFiber source s) // P.card = 2}

/-- Embed a common-source fiber into the full skeleton by retaining the
length-two middle term. -/
def commonSourceEdgeEmbedding
    (source : σ.LengthTwoIndex → σ.SimpleIndex)
    (s : σ.SimpleIndex) :
    σ.CommonSourceFiber source s ↪ ι where
  toFun e := e.1.1
  inj' e e' h := by
    apply Subtype.ext
    apply Subtype.ext
    exact h

/-- The two length-two indices selected by a common-source pair. -/
def commonSourcePairEdgeSet
    (source : σ.LengthTwoIndex → σ.SimpleIndex)
    (p : σ.CommonSourcePair source) : Set ι :=
  σ.commonSourceEdgeEmbedding source p.1 ''
    (p.2.1 : Set (σ.CommonSourceFiber source p.1))

/-- The family-3 support: the two length-two objects and their common
simple top. -/
def commonSourcePairSupport
    (source : σ.LengthTwoIndex → σ.SimpleIndex)
    (p : σ.CommonSourcePair source) : Set ι :=
  insert p.1.1 (σ.commonSourcePairEdgeSet source p)

@[simp]
theorem ncard_commonSourcePairEdgeSet
    (source : σ.LengthTwoIndex → σ.SimpleIndex)
    (p : σ.CommonSourcePair source) :
    (σ.commonSourcePairEdgeSet source p).ncard = 2 := by
  rw [commonSourcePairEdgeSet,
    Set.ncard_image_of_injective _
      (σ.commonSourceEdgeEmbedding source p.1).injective,
    Set.ncard_coe_finset, p.2.2]

theorem source_not_mem_commonSourcePairEdgeSet
    (source : σ.LengthTwoIndex → σ.SimpleIndex)
    (p : σ.CommonSourcePair source) :
    p.1.1 ∉ σ.commonSourcePairEdgeSet source p := by
  rintro ⟨e, -, he⟩
  exact σ.lengthTwoIndex_ne_simpleIndex e.1 p.1 he

@[simp]
theorem ncard_commonSourcePairSupport
    (source : σ.LengthTwoIndex → σ.SimpleIndex)
    (p : σ.CommonSourcePair source) :
    (σ.commonSourcePairSupport source p).ncard = 3 := by
  have hfinite :
      (σ.commonSourcePairEdgeSet source p).Finite :=
    p.2.1.finite_toSet.image
      (σ.commonSourceEdgeEmbedding source p.1)
  rw [commonSourcePairSupport,
    Set.ncard_insert_of_notMem
      (σ.source_not_mem_commonSourcePairEdgeSet source p) hfinite,
    σ.ncard_commonSourcePairEdgeSet source p]

theorem commonSourcePairEdgeSet_injective_at
    (source : σ.LengthTwoIndex → σ.SimpleIndex)
    (s : σ.SimpleIndex) :
    Function.Injective
      (fun P : {P : Finset (σ.CommonSourceFiber source s) // P.card = 2} ↦
        σ.commonSourceEdgeEmbedding source s ''
          (P.1 : Set (σ.CommonSourceFiber source s))) := by
  intro P Q hPQ
  apply Subtype.ext
  apply Finset.ext
  intro e
  constructor
  · intro he
    have heImage :
      σ.commonSourceEdgeEmbedding source s e ∈
          σ.commonSourceEdgeEmbedding source s ''
            (P.1 : Set (σ.CommonSourceFiber source s)) :=
      ⟨e, he, rfl⟩
    rw [show
      σ.commonSourceEdgeEmbedding source s ''
          (P.1 : Set (σ.CommonSourceFiber source s)) =
        σ.commonSourceEdgeEmbedding source s ''
          (Q.1 : Set (σ.CommonSourceFiber source s)) from hPQ]
      at heImage
    rcases heImage with ⟨e', he', he'e⟩
    have heq : e' = e :=
      (σ.commonSourceEdgeEmbedding source s).injective he'e
    simpa [heq] using he'
  · intro he
    have heImage :
        σ.commonSourceEdgeEmbedding source s e ∈
          σ.commonSourceEdgeEmbedding source s ''
            (Q.1 : Set (σ.CommonSourceFiber source s)) :=
      ⟨e, he, rfl⟩
    rw [show
      σ.commonSourceEdgeEmbedding source s ''
          (Q.1 : Set (σ.CommonSourceFiber source s)) =
        σ.commonSourceEdgeEmbedding source s ''
          (P.1 : Set (σ.CommonSourceFiber source s)) from hPQ.symm]
      at heImage
    rcases heImage with ⟨e', he', he'e⟩
    have heq : e' = e :=
      (σ.commonSourceEdgeEmbedding source s).injective he'e
    simpa [heq] using he'

theorem commonSourcePairSupport_injective
    (source : σ.LengthTwoIndex → σ.SimpleIndex) :
    Function.Injective (σ.commonSourcePairSupport source) := by
  rintro ⟨s, P⟩ ⟨s', Q⟩ hsupport
  have hsMem :
      s.1 ∈ σ.commonSourcePairSupport source ⟨s', Q⟩ := by
    rw [← hsupport]
    simp [commonSourcePairSupport]
  have hss' : s = s' := by
    rcases (by
      simpa [commonSourcePairSupport] using hsMem) with h | h
    · exact Subtype.ext h
    · rcases h with ⟨e, -, he⟩
      exact False.elim
        (σ.lengthTwoIndex_ne_simpleIndex e.1 s he)
  subst s'
  have hedgeSet :
      σ.commonSourceEdgeEmbedding source s ''
          (P.1 : Set (σ.CommonSourceFiber source s)) =
        σ.commonSourceEdgeEmbedding source s ''
          (Q.1 : Set (σ.CommonSourceFiber source s)) := by
    ext i
    constructor
    · intro hi
      have hiSupport :
          i ∈ σ.commonSourcePairSupport source ⟨s, P⟩ := by
        exact Or.inr hi
      rw [hsupport] at hiSupport
      rcases (by
        simpa [commonSourcePairSupport] using hiSupport) with his | hiQ
      · rcases hi with ⟨e, -, hei⟩
        exact False.elim
          (σ.lengthTwoIndex_ne_simpleIndex e.1 s
            (hei.trans his))
      · exact hiQ
    · intro hi
      have hiSupport :
          i ∈ σ.commonSourcePairSupport source ⟨s, Q⟩ := by
        exact Or.inr hi
      rw [← hsupport] at hiSupport
      rcases (by
        simpa [commonSourcePairSupport] using hiSupport) with his | hiP
      · rcases hi with ⟨e, -, hei⟩
        exact False.elim
          (σ.lengthTwoIndex_ne_simpleIndex e.1 s
            (hei.trans his))
      · exact hiP
  have hPQ : P = Q :=
    σ.commonSourcePairEdgeSet_injective_at source s hedgeSet
  subst Q
  rfl

/-- The only indecomposable quotients of a length-two representative are
itself and the index of any chosen simple quotient. -/
theorem quotient_index_eq_lengthTwo_or_top
    (e : σ.LengthTwoIndex)
    (Q : σ.SimpleQuotient e.1)
    {j : ι} (f : σ.obj e.1 ⟶ σ.obj j) [Epi f] :
    j = e.1 ∨ j = Q.index := by
  rcases
      σ.simple_or_isIso_of_epi_of_compositionLength_eq_two
        f e.2 with hjSimple | hfIso
  · right
    let Q' : σ.SimpleQuotient e.1 := {
      index := j
      simple := hjSimple
      map := f
      epi := inferInstance }
    exact
      SimpleQuotient.index_eq_of_compositionLength_eq_two
        σ e.2 Q' Q
  · left
    exact (σ.eq_of_iso ⟨@asIso _ _ _ _ _ hfIso⟩).symm

/-- Family 3 is closed under quotients of each selected object separately.
The source is taken from explicit simple-quotient data, so no Gabriel input
is used here. -/
theorem individuallyQuotientClosed_commonSourcePairSupport
    (top : ∀ e : σ.LengthTwoIndex, σ.SimpleQuotient e.1)
    (p : σ.CommonSourcePair
      (fun e ↦ ⟨(top e).index, (top e).simple⟩)) :
    σ.IndividuallyQuotientClosed
      (σ.commonSourcePairSupport
        (fun e ↦ ⟨(top e).index, (top e).simple⟩) p) := by
  intro i j hi f hf
  letI : Epi f := hf
  rcases (by
    simpa [commonSourcePairSupport] using hi) with his | hiEdge
  · have hj : j = p.1.1 :=
      σ.index_eq_of_epi_from_simple p.1.2
        (eqToHom (congrArg σ.obj his.symm) ≫ f)
    simp [commonSourcePairSupport, hj]
  · rcases hiEdge with ⟨e, heP, hei⟩
    have heq : i = e.1.1 := hei.symm
    let g : σ.obj e.1.1 ⟶ σ.obj j :=
      eqToHom (congrArg σ.obj heq.symm) ≫ f
    letI : Epi g := by
      dsimp only [g]
      infer_instance
    rcases σ.quotient_index_eq_lengthTwo_or_top e.1 (top e.1) g with
      hjEdge | hjTop
    · right
      exact ⟨e, heP, hjEdge.symm⟩
    · left
      have hsource :
          ((⟨(top e.1).index, (top e.1).simple⟩ : σ.SimpleIndex)).1 =
            p.1.1 :=
        congrArg Subtype.val e.2
      exact hjTop.trans hsource

/-- The remaining collective condition for family 3: every indecomposable
generated by the common-top support has simple top. -/
def CommonSourcePairFacTargetsHaveSimpleTop
    (source : σ.LengthTwoIndex → σ.SimpleIndex)
    (p : σ.CommonSourcePair source) : Prop :=
  ∀ {j : ι},
    σ.InFac (σ.commonSourcePairSupport source p) (σ.obj j) →
      IsSimpleModule R (σ.moduleTop j)

theorem commonSourcePairFacPresentationsHaveEpiComponent_of_targetsHaveSimpleTop
    (source : σ.LengthTwoIndex → σ.SimpleIndex)
    (p : σ.CommonSourcePair source)
    (htop : σ.CommonSourcePairFacTargetsHaveSimpleTop source p) :
    σ.FacPresentationsHaveEpiComponent
      (σ.commonSourcePairSupport source p) := by
  intro j P
  letI : Epi P.map := P.epi
  exact
    σ.exists_epi_biproduct_component_of_simple_top
      P.index P.label (htop ⟨P⟩) P.map

/-- Closedness of a common-source support forces the simple-top condition,
because every member is either the common simple source or one of the two
length-two objects. -/
theorem commonSourcePairFacTargetsHaveSimpleTop_of_qClosure_isClosed
    (source : σ.LengthTwoIndex → σ.SimpleIndex)
    (p : σ.CommonSourcePair source)
    (hclosed : σ.qClosure.IsClosed
      (σ.commonSourcePairSupport source p)) :
    σ.CommonSourcePairFacTargetsHaveSimpleTop source p := by
  intro j hj
  have hjMem : j ∈ σ.commonSourcePairSupport source p := by
    rw [← hclosed.closure_eq]
    exact hj
  rcases (by
    simpa [commonSourcePairSupport] using hjMem) with hjs | hjEdge
  · subst j
    exact σ.moduleTop_isSimple_of_simple p.1.2
  · rcases hjEdge with ⟨e, -, hej⟩
    have hje : j = e.1.1 := hej.symm
    subst j
    exact
      QuotientSubmoduleEquidistribution.BottomTwoSimpleTop.IndecomposableSkeleton.moduleTop_isSimple_of_compositionLength_eq_two
        σ e.1.2

/-- Exact collective-closure reduction for family 3.  The forward direction
uses no extra hypotheses; the reverse direction uses the unconditional
individual quotient classification above. -/
theorem qClosure_isClosed_commonSourcePairSupport_iff_targetsHaveSimpleTop
    (top : ∀ e : σ.LengthTwoIndex, σ.SimpleQuotient e.1)
    (p : σ.CommonSourcePair
      (fun e ↦ ⟨(top e).index, (top e).simple⟩)) :
    σ.qClosure.IsClosed
        (σ.commonSourcePairSupport
          (fun e ↦ ⟨(top e).index, (top e).simple⟩) p) ↔
      σ.CommonSourcePairFacTargetsHaveSimpleTop
        (fun e ↦ ⟨(top e).index, (top e).simple⟩) p := by
  constructor
  · exact
      σ.commonSourcePairFacTargetsHaveSimpleTop_of_qClosure_isClosed
        (fun e ↦ ⟨(top e).index, (top e).simple⟩) p
  · intro htop
    exact
      σ.qClosure_isClosed_of_individual_of_epiComponent
        (σ.individuallyQuotientClosed_commonSourcePairSupport top p)
        (σ.commonSourcePairFacPresentationsHaveEpiComponent_of_targetsHaveSimpleTop
          (fun e ↦ ⟨(top e).index, (top e).simple⟩) p htop)

/-- Every simple quotient of an indecomposable generated by a common-source
pair has the common source index.  Thus the unresolved simple-top assertion
is purely multiplicity one, not identification of the simple type. -/
theorem simpleQuotient_index_eq_of_inFac_commonSourcePair
    (top : ∀ e : σ.LengthTwoIndex, σ.SimpleQuotient e.1)
    (p : σ.CommonSourcePair
      (fun e ↦ ⟨(top e).index, (top e).simple⟩))
    {j : ι}
    (hj : σ.InFac
      (σ.commonSourcePairSupport
        (fun e ↦ ⟨(top e).index, (top e).simple⟩) p)
      (σ.obj j))
    (L : σ.SimpleQuotient j) :
    L.index = p.1.1 := by
  classical
  obtain ⟨P⟩ := hj
  let g : σ.sumOver P.index P.label ⟶ σ.obj L.index :=
    P.map ≫ L.map
  letI : Epi P.map := P.epi
  letI : Epi L.map := L.epi
  letI : Epi g := by
    dsimp only [g]
    infer_instance
  letI : Simple (σ.obj L.index) := L.simple
  have hg : g ≠ 0 := by
    intro hzero
    exact
      (Simple.not_isZero (σ.obj L.index))
        (IsZero.of_epi_eq_zero g hzero)
  have hcomponent :
      ∃ t : P.index,
        biproduct.ι
            (fun a : P.index ↦ σ.obj (P.label a)) t ≫
          g ≠ 0 := by
    by_contra h
    push Not at h
    apply hg
    apply biproduct.hom_ext'
    intro t
    simpa using h t
  obtain ⟨t, ht⟩ := hcomponent
  let f : σ.obj (P.label t) ⟶ σ.obj L.index :=
    biproduct.ι
        (fun a : P.index ↦ σ.obj (P.label a)) t ≫
      g
  letI : Epi f := epi_of_nonzero_to_simple ht
  have hlabel := P.mem t
  rcases (by
    simpa [commonSourcePairSupport] using hlabel) with
    hsource | hedge
  · letI : Simple (σ.obj (P.label t)) := by
      simpa [hsource] using p.1.2
    haveI : IsIso f := isIso_of_hom_simple ht
    have hindex : P.label t = L.index :=
      σ.eq_of_iso ⟨asIso f⟩
    exact hindex.symm.trans hsource
  · rcases hedge with ⟨e, -, heLabel⟩
    let f' : σ.obj e.1.1 ⟶ σ.obj L.index :=
      eqToHom (congrArg σ.obj heLabel) ≫ f
    letI : Epi f' := by
      dsimp only [f']
      infer_instance
    let Q' : σ.SimpleQuotient e.1.1 := {
      index := L.index
      simple := L.simple
      map := f'
      epi := inferInstance }
    have htop : L.index = (top e.1).index :=
      SimpleQuotient.index_eq_of_compositionLength_eq_two
        σ e.1.2 Q' (top e.1)
    have hsource :
        (top e.1).index = p.1.1 :=
      congrArg Subtype.val e.2
    exact htop.trans hsource

theorem hasUniqueSimpleQuotientType_of_inFac_commonSourcePair
    (top : ∀ e : σ.LengthTwoIndex, σ.SimpleQuotient e.1)
    (p : σ.CommonSourcePair
      (fun e ↦ ⟨(top e).index, (top e).simple⟩))
    {j : ι}
    (hj : σ.InFac
      (σ.commonSourcePairSupport
        (fun e ↦ ⟨(top e).index, (top e).simple⟩) p)
      (σ.obj j)) :
    σ.HasUniqueSimpleQuotientType j p.1.1 :=
  ⟨p.1.2,
    fun L ↦
      σ.simpleQuotient_index_eq_of_inFac_commonSourcePair top p hj L⟩

/-- The semisimple top of every family-3 generated target is isotypic of
the common simple top. -/
theorem moduleTop_isIsotypicOfType_of_inFac_commonSourcePair
    (top : ∀ e : σ.LengthTwoIndex, σ.SimpleQuotient e.1)
    (p : σ.CommonSourcePair
      (fun e ↦ ⟨(top e).index, (top e).simple⟩))
    {j : ι}
    (hj : σ.InFac
      (σ.commonSourcePairSupport
        (fun e ↦ ⟨(top e).index, (top e).simple⟩) p)
      (σ.obj j)) :
    IsIsotypicOfType R (σ.moduleTop j) (σ.obj p.1.1) :=
  QuotientSubmoduleEquidistribution.LevelTwoUnconditional.moduleTop_isIsotypicOfType_of_hasUniqueSimpleQuotientType
    σ
    (σ.hasUniqueSimpleQuotientType_of_inFac_commonSourcePair top p hj)

/-- Conditional injective realization of family 3 into the actual third
closure level.  The hypothesis is now exactly the unresolved common-top
multiplicity-one statement. -/
def commonSourcePairToClosedLevelThree
    (top : ∀ e : σ.LengthTwoIndex, σ.SimpleQuotient e.1)
    (htop : ∀ p : σ.CommonSourcePair
      (fun e ↦ ⟨(top e).index, (top e).simple⟩),
      σ.CommonSourcePairFacTargetsHaveSimpleTop
        (fun e ↦ ⟨(top e).index, (top e).simple⟩) p)
    (p : σ.CommonSourcePair
      (fun e ↦ ⟨(top e).index, (top e).simple⟩)) :
    QuotientSubmoduleEquidistribution.BottomLevels.BottomThreeAdapter.ClosedLevelThree
      σ.qClosure :=
  ⟨⟨σ.commonSourcePairSupport
        (fun e ↦ ⟨(top e).index, (top e).simple⟩) p,
      (σ.qClosure_isClosed_commonSourcePairSupport_iff_targetsHaveSimpleTop
        top p).2 (htop p)⟩,
    σ.ncard_commonSourcePairSupport
      (fun e ↦ ⟨(top e).index, (top e).simple⟩) p⟩

theorem commonSourcePairToClosedLevelThree_injective
    (top : ∀ e : σ.LengthTwoIndex, σ.SimpleQuotient e.1)
    (htop : ∀ p : σ.CommonSourcePair
      (fun e ↦ ⟨(top e).index, (top e).simple⟩),
      σ.CommonSourcePairFacTargetsHaveSimpleTop
        (fun e ↦ ⟨(top e).index, (top e).simple⟩) p) :
    Function.Injective
      (σ.commonSourcePairToClosedLevelThree top htop) := by
  intro p q hpq
  apply σ.commonSourcePairSupport_injective
    (fun e ↦ ⟨(top e).index, (top e).simple⟩)
  exact congrArg (fun C ↦ (C.1.1 : Set ι)) hpq

/-! ## Family 2 under the manuscript hypotheses -/

universe x

/-- Under the paper's finite-dimensional algebraically closed hypotheses,
the edge-plus-extra-simple family is unconditionally collectively closed.
This combines the existing no-parallel one-arrow theorem for the
length-two/top pair with the new simple-adjunction theorem above. -/
theorem qClosure_isClosed_gabrielEdgeExtraSimpleSupport
    (K A : Type x)
    [Field K] [IsAlgClosed K]
    [Ring A] [Algebra K A] [FiniteDimensional K A] :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K A
    ∀ {κ : Type x} [Finite κ]
      (τ : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{x, x, x} Aᵐᵒᵖ κ)
      (p : τ.EdgeExtraSimple
        (QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.source τ)),
      τ.qClosure.IsClosed
        (τ.edgeExtraSimpleSupport
          (QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.source τ) p) := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K A
  intro κ _ τ p
  apply τ.qClosure_isClosed_edgeExtraSimpleSupport
    (QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.source τ)
  intro e
  exact
    QuotientSubmoduleEquidistribution.LoewyTwoGabrielClassification.qClosure_isClosed_length_two_top_pair
      K A τ e.2
      (QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.quotient τ e)
      (QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.submodule τ e)

/-- The corresponding unconditional injective realization of formal family
2 in the actual third quotient-closure level. -/
noncomputable def gabrielEdgeExtraSimpleToClosedLevelThree
    (K A : Type x)
    [Field K] [IsAlgClosed K]
    [Ring A] [Algebra K A] [FiniteDimensional K A] :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K A
    ∀ {κ : Type x} [Finite κ]
      (τ : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{x, x, x} Aᵐᵒᵖ κ),
      τ.EdgeExtraSimple
          (QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.source τ) →
        QuotientSubmoduleEquidistribution.BottomLevels.BottomThreeAdapter.ClosedLevelThree
          τ.qClosure := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K A
  intro κ _ τ
  exact τ.edgeExtraSimpleToClosedLevelThree
    (QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.source τ)
    (fun e ↦
      QuotientSubmoduleEquidistribution.LoewyTwoGabrielClassification.qClosure_isClosed_length_two_top_pair
        K A τ e.2
        (QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.quotient τ e)
        (QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.submodule τ e))

theorem gabrielEdgeExtraSimpleToClosedLevelThree_injective
    (K A : Type x)
    [Field K] [IsAlgClosed K]
    [Ring A] [Algebra K A] [FiniteDimensional K A] :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K A
    ∀ {κ : Type x} [Finite κ]
      (τ : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{x, x, x} Aᵐᵒᵖ κ),
      Function.Injective
        (gabrielEdgeExtraSimpleToClosedLevelThree K A τ) := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K A
  intro κ _ τ
  exact τ.edgeExtraSimpleToClosedLevelThree_injective
    (QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.source τ)
    (fun e ↦
      QuotientSubmoduleEquidistribution.LoewyTwoGabrielClassification.qClosure_isClosed_length_two_top_pair
        K A τ e.2
        (QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.quotient τ e)
        (QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.submodule τ e))

/-! ## Family 5: a two-top length-three object -/

/-- The skeleton indices which occur as simple quotients of `i`. -/
def simpleQuotientIndexSet (i : ι) : Set ι :=
  {s | ∃ Q : σ.SimpleQuotient i, Q.index = s}

theorem simple_of_mem_simpleQuotientIndexSet
    {i s : ι} (hs : s ∈ σ.simpleQuotientIndexSet i) :
    Simple (σ.obj s) := by
  rcases hs with ⟨Q, rfl⟩
  exact Q.simple

/-- Quotient-theoretic content of the manuscript's family-5 apex:

* composition length three;
* exactly two simple quotient types;
* no indecomposable quotient of composition length two.

For the stated Loewy-length-two module with two distinct simple top
summands and simple radical, these are the exact objectwise consequences
needed below.  Deriving this predicate from that radical/top description is
kept separate from collective closure. -/
def IsTwoTopQuotientShape (i : ι) : Prop :=
  σ.compositionLength i = 3 ∧
    (σ.simpleQuotientIndexSet i).ncard = 2 ∧
      ∀ {j : ι} (f : σ.obj i ⟶ σ.obj j),
        Epi f → σ.compositionLength j ≠ 2

/-- Actual skeleton indices with the family-5 objectwise quotient shape. -/
def TwoTopQuotientShapeIndex :=
  {i : ι // σ.IsTwoTopQuotientShape i}

/-- The apex together with its two simple quotient types. -/
def twoTopQuotientShapeSupport
    (x : σ.TwoTopQuotientShapeIndex) : Set ι :=
  insert x.1 (σ.simpleQuotientIndexSet x.1)

theorem twoTopQuotientShapeIndex_not_mem_simpleQuotients
    (x : σ.TwoTopQuotientShapeIndex) :
    x.1 ∉ σ.simpleQuotientIndexSet x.1 := by
  intro hx
  have hsimple : Simple (σ.obj x.1) :=
    σ.simple_of_mem_simpleQuotientIndexSet hx
  have hone : σ.compositionLength x.1 = 1 :=
    (σ.compositionLength_eq_one_iff_simple x.1).2 hsimple
  have hshape := x.2
  unfold IsTwoTopQuotientShape at hshape
  omega

@[simp]
theorem ncard_twoTopQuotientShapeSupport
    (x : σ.TwoTopQuotientShapeIndex) :
    (σ.twoTopQuotientShapeSupport x).ncard = 3 := by
  have hfinite : (σ.simpleQuotientIndexSet x.1).Finite :=
    Set.finite_of_ncard_ne_zero (by
      rw [x.2.2.1]
      decide)
  rw [twoTopQuotientShapeSupport,
    Set.ncard_insert_of_notMem
      (σ.twoTopQuotientShapeIndex_not_mem_simpleQuotients x) hfinite,
    x.2.2.1]

theorem twoTopQuotientShapeSupport_injective :
    Function.Injective σ.twoTopQuotientShapeSupport := by
  intro x y hxy
  apply Subtype.ext
  have hxMem : x.1 ∈ σ.twoTopQuotientShapeSupport y := by
    rw [← hxy]
    simp [twoTopQuotientShapeSupport]
  rcases (by
    simpa [twoTopQuotientShapeSupport] using hxMem) with hxy' | hxSimple
  · exact hxy'
  · have hsimple : Simple (σ.obj x.1) :=
      σ.simple_of_mem_simpleQuotientIndexSet hxSimple
    have hone : σ.compositionLength x.1 = 1 :=
      (σ.compositionLength_eq_one_iff_simple x.1).2 hsimple
    have hshape := x.2
    unfold IsTwoTopQuotientShape at hshape
    omega

/-- Family 5 is closed under quotients of each selected object separately.
This uses exactly the absence of a length-two indecomposable quotient in
`IsTwoTopQuotientShape`. -/
theorem individuallyQuotientClosed_twoTopQuotientShapeSupport
    (x : σ.TwoTopQuotientShapeIndex) :
    σ.IndividuallyQuotientClosed
      (σ.twoTopQuotientShapeSupport x) := by
  intro i j hi f hf
  letI : Epi f := hf
  rcases (by
    simpa [twoTopQuotientShapeSupport] using hi) with hix | hiSimple
  · let g : σ.obj x.1 ⟶ σ.obj j :=
      eqToHom (congrArg σ.obj hix.symm) ≫ f
    letI : Epi g := by
      dsimp only [g]
      infer_instance
    rcases
        σ.simple_or_lengthTwo_or_isIso_of_epi_of_compositionLength_eq_three
          g x.2.1 with hjSimple | hjLength | hgIso
    · right
      exact ⟨{
        index := j
        simple := hjSimple
        map := g
        epi := inferInstance }, rfl⟩
    · exact False.elim (x.2.2.2 g inferInstance hjLength)
    · left
      exact (σ.eq_of_iso ⟨@asIso _ _ _ _ _ hgIso⟩).symm
  · have hiIsSimple : Simple (σ.obj i) :=
      σ.simple_of_mem_simpleQuotientIndexSet hiSimple
    have hji : j = i :=
      σ.index_eq_of_epi_from_simple hiIsSimple f
    subst j
    exact Or.inr hiSimple

/-- The remaining collective family-5 input, stated without disguising it
as objectwise quotient closure. -/
def TwoTopQuotientShapeFacPresentationsHaveEpiComponent
    (x : σ.TwoTopQuotientShapeIndex) : Prop :=
  σ.FacPresentationsHaveEpiComponent
    (σ.twoTopQuotientShapeSupport x)

/-- The epic-component input is sufficient for the actual family-5 support
to be collectively quotient closed. -/
theorem qClosure_isClosed_twoTopQuotientShapeSupport_of_epiComponent
    (x : σ.TwoTopQuotientShapeIndex)
    (hcomponent :
      σ.TwoTopQuotientShapeFacPresentationsHaveEpiComponent x) :
    σ.qClosure.IsClosed (σ.twoTopQuotientShapeSupport x) :=
  σ.qClosure_isClosed_of_individual_of_epiComponent
    (σ.individuallyQuotientClosed_twoTopQuotientShapeSupport x)
    hcomponent

/-! ### Matching the common-target arrow-pair parameter -/

/-- The formal common-target arrow-pair parameter used by family 5. -/
abbrev CommonTargetPair
    (target : σ.LengthTwoIndex → σ.SimpleIndex) :=
  Σ t : σ.SimpleIndex,
    {P : Finset {e : σ.LengthTwoIndex // target e = t} // P.card = 2}

/-- The two simple sources belonging to a common-target arrow pair, embedded
in the full skeleton. -/
def commonTargetPairSourceSet
    (source target : σ.LengthTwoIndex → σ.SimpleIndex)
    (p : σ.CommonTargetPair target) : Set ι :=
  (fun e : {e : σ.LengthTwoIndex // target e = p.1} ↦
      (source e.1).1) ''
    (p.2.1 : Set {e : σ.LengthTwoIndex // target e = p.1})

/-- Exact construction interface for the manuscript's fifth family.

`apex` constructs the length-three module from the two common-target arrows;
`simpleQuotients_eq_sources` identifies its two top simples; injectivity is
the uniqueness of that apex construction; `collective` is the remaining
arbitrary-biproduct closure assertion. -/
structure CommonTargetForkRealization
    (source target : σ.LengthTwoIndex → σ.SimpleIndex) where
  apex : σ.CommonTargetPair target →
    σ.TwoTopQuotientShapeIndex
  simpleQuotients_eq_sources :
    ∀ p, σ.simpleQuotientIndexSet (apex p).1 =
      σ.commonTargetPairSourceSet source target p
  apex_injective : Function.Injective apex
  collective : ∀ p,
    σ.TwoTopQuotientShapeFacPresentationsHaveEpiComponent (apex p)

namespace CommonTargetForkRealization

/-- A supplied common-target fork construction gives actual closed
three-element supports. -/
def toClosedLevelThree
    {source target : σ.LengthTwoIndex → σ.SimpleIndex}
    (D : σ.CommonTargetForkRealization source target)
    (p : σ.CommonTargetPair target) :
    QuotientSubmoduleEquidistribution.BottomLevels.BottomThreeAdapter.ClosedLevelThree
      σ.qClosure :=
  ⟨⟨σ.twoTopQuotientShapeSupport (D.apex p),
      σ.qClosure_isClosed_twoTopQuotientShapeSupport_of_epiComponent
        (D.apex p) (D.collective p)⟩,
    σ.ncard_twoTopQuotientShapeSupport (D.apex p)⟩

theorem toClosedLevelThree_injective
    {source target : σ.LengthTwoIndex → σ.SimpleIndex}
    (D : σ.CommonTargetForkRealization source target) :
    Function.Injective D.toClosedLevelThree := by
  intro p q hpq
  apply D.apex_injective
  apply σ.twoTopQuotientShapeSupport_injective
  exact congrArg (fun C ↦ (C.1.1 : Set ι)) hpq

end CommonTargetForkRealization

/-! ## Separation of the four non-uniserial families -/

theorem simple_or_lengthTwo_of_mem_edgeExtraSimpleSupport
    (source : σ.LengthTwoIndex → σ.SimpleIndex)
    (p : σ.EdgeExtraSimple source) {i : ι}
    (hi : i ∈ σ.edgeExtraSimpleSupport source p) :
    Simple (σ.obj i) ∨ σ.compositionLength i = 2 := by
  rcases (by
    simpa [edgeExtraSimpleSupport] using hi) with h | h | h
  · right
    simpa [h] using p.1.2
  · left
    simpa [h] using (source p.1).2
  · left
    simpa [h] using p.2.1.2

theorem simple_or_lengthTwo_of_mem_commonSourcePairSupport
    (source : σ.LengthTwoIndex → σ.SimpleIndex)
    (p : σ.CommonSourcePair source) {i : ι}
    (hi : i ∈ σ.commonSourcePairSupport source p) :
    Simple (σ.obj i) ∨ σ.compositionLength i = 2 := by
  rcases (by
    simpa [commonSourcePairSupport] using hi) with h | h
  · left
    simpa [h] using p.1.2
  · rcases h with ⟨e, -, hei⟩
    right
    change e.1.1 = i at hei
    simpa [← hei] using e.1.2

theorem eq_apex_or_simple_of_mem_twoTopQuotientShapeSupport
    (x : σ.TwoTopQuotientShapeIndex) {i : ι}
    (hi : i ∈ σ.twoTopQuotientShapeSupport x) :
    i = x.1 ∨ Simple (σ.obj i) := by
  rcases (by
    simpa [twoTopQuotientShapeSupport] using hi) with h | h
  · exact Or.inl h
  · exact Or.inr (σ.simple_of_mem_simpleQuotientIndexSet h)

/-- A simple member of a common-source support is necessarily the common
source itself. -/
theorem simpleIndex_eq_source_of_mem_commonSourcePairSupport
    (source : σ.LengthTwoIndex → σ.SimpleIndex)
    (p : σ.CommonSourcePair source)
    (s : σ.SimpleIndex)
    (hs : s.1 ∈ σ.commonSourcePairSupport source p) :
    s = p.1 := by
  rcases (by
    simpa [commonSourcePairSupport] using hs) with h | h
  · exact Subtype.ext h
  · rcases h with ⟨e, -, hes⟩
    change e.1.1 = s.1 at hes
    exact False.elim
      (σ.lengthTwoIndex_ne_simpleIndex e.1 s hes)

theorem simpleTripleSupport_ne_edgeExtraSimpleSupport
    (P : σ.SimpleTriple)
    (source : σ.LengthTwoIndex → σ.SimpleIndex)
    (p : σ.EdgeExtraSimple source) :
    σ.simpleTripleSupport P ≠
      σ.edgeExtraSimpleSupport source p := by
  intro h
  have heMem : p.1.1 ∈ σ.simpleTripleSupport P := by
    rw [h]
    simp [edgeExtraSimpleSupport]
  exact σ.lengthTwoIndex_not_simple p.1
    (σ.simple_of_mem_simpleTripleSupport P heMem)

theorem simpleTripleSupport_ne_commonSourcePairSupport
    (P : σ.SimpleTriple)
    (source : σ.LengthTwoIndex → σ.SimpleIndex)
    (p : σ.CommonSourcePair source) :
    σ.simpleTripleSupport P ≠
      σ.commonSourcePairSupport source p := by
  intro h
  have hcard : p.2.1.card = 2 := p.2.2
  have hpos : 0 < p.2.1.card := by omega
  obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
  have heMem : e.1.1 ∈ σ.simpleTripleSupport P := by
    rw [h]
    right
    exact ⟨e, he, rfl⟩
  exact σ.lengthTwoIndex_not_simple e.1
    (σ.simple_of_mem_simpleTripleSupport P heMem)

theorem simpleTripleSupport_ne_twoTopQuotientShapeSupport
    (P : σ.SimpleTriple)
    (x : σ.TwoTopQuotientShapeIndex) :
    σ.simpleTripleSupport P ≠
      σ.twoTopQuotientShapeSupport x := by
  intro h
  have hxMem : x.1 ∈ σ.simpleTripleSupport P := by
    rw [h]
    simp [twoTopQuotientShapeSupport]
  have hxSimple := σ.simple_of_mem_simpleTripleSupport P hxMem
  have hone : σ.compositionLength x.1 = 1 :=
    (σ.compositionLength_eq_one_iff_simple x.1).2 hxSimple
  have hshape := x.2
  unfold IsTwoTopQuotientShape at hshape
  omega

theorem edgeExtraSimpleSupport_ne_commonSourcePairSupport
    (source : σ.LengthTwoIndex → σ.SimpleIndex)
    (p : σ.EdgeExtraSimple source)
    (source' : σ.LengthTwoIndex → σ.SimpleIndex)
    (q : σ.CommonSourcePair source') :
    σ.edgeExtraSimpleSupport source p ≠
      σ.commonSourcePairSupport source' q := by
  intro h
  have hsMem :
      (source p.1).1 ∈
        σ.commonSourcePairSupport source' q := by
    rw [← h]
    simp [edgeExtraSimpleSupport]
  have htMem :
      p.2.1.1 ∈
        σ.commonSourcePairSupport source' q := by
    rw [← h]
    simp [edgeExtraSimpleSupport]
  have hsEq : source p.1 = q.1 :=
    σ.simpleIndex_eq_source_of_mem_commonSourcePairSupport
      source' q (source p.1) hsMem
  have htEq : p.2.1 = q.1 :=
    σ.simpleIndex_eq_source_of_mem_commonSourcePairSupport
      source' q p.2.1 htMem
  exact p.2.2 (htEq.trans hsEq.symm)

theorem edgeExtraSimpleSupport_ne_twoTopQuotientShapeSupport
    (source : σ.LengthTwoIndex → σ.SimpleIndex)
    (p : σ.EdgeExtraSimple source)
    (x : σ.TwoTopQuotientShapeIndex) :
    σ.edgeExtraSimpleSupport source p ≠
      σ.twoTopQuotientShapeSupport x := by
  intro h
  have heMem : p.1.1 ∈ σ.twoTopQuotientShapeSupport x := by
    rw [← h]
    simp [edgeExtraSimpleSupport]
  rcases σ.eq_apex_or_simple_of_mem_twoTopQuotientShapeSupport x heMem with
    heApex | heSimple
  · have hshape := x.2
    unfold IsTwoTopQuotientShape at hshape
    have heLength := p.1.2
    rw [heApex] at heLength
    omega
  · exact σ.lengthTwoIndex_not_simple p.1 heSimple

theorem commonSourcePairSupport_ne_twoTopQuotientShapeSupport
    (source : σ.LengthTwoIndex → σ.SimpleIndex)
    (p : σ.CommonSourcePair source)
    (x : σ.TwoTopQuotientShapeIndex) :
    σ.commonSourcePairSupport source p ≠
      σ.twoTopQuotientShapeSupport x := by
  intro h
  have hcard : p.2.1.card = 2 := p.2.2
  have hpos : 0 < p.2.1.card := by omega
  obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
  have heMem : e.1.1 ∈ σ.twoTopQuotientShapeSupport x := by
    rw [← h]
    right
    exact ⟨e, he, rfl⟩
  rcases σ.eq_apex_or_simple_of_mem_twoTopQuotientShapeSupport x heMem with
    heApex | heSimple
  · have hshape := x.2
    unfold IsTwoTopQuotientShape at hshape
    have heLength := e.1.2
    rw [heApex] at heLength
    omega
  · exact σ.lengthTwoIndex_not_simple e.1 heSimple

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
