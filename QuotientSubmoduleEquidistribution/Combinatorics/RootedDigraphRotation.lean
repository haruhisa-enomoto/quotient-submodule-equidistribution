import QuotientSubmoduleEquidistribution.Combinatorics.RootedDigraph

/-!
# Rotation of grouped top-part data

This file isolates the precise graph-theoretic content of AR mesh rotation.
The rotation is an anti-isomorphism on nonboundary vertices and identifies
incoming arrows at a source support with incoming arrows at its rotated
target support without relabeling the other endpoint.  These two clauses are
exactly what is used in the rooted-balance inclusion--exclusion argument.
-/

noncomputable section

namespace QuotientSubmoduleEquidistribution.RootedDigraph

universe u

variable {Vertex : Type u} [Fintype Vertex] [DecidableEq Vertex]

/-- The graph-theoretic mesh-rotation interface behind rooted balance. -/
structure GroupedRotationData
    (qEdge sEdge : Vertex → Vertex → Prop)
    (P I : Finset Vertex) where
  perm : Equiv.Perm Vertex
  nonboundary_iff : ∀ x, x ∉ P ↔ perm x ∉ I
  edge_iff : ∀ {x y}, x ∉ P → y ∉ P →
    (qEdge x y ↔ sEdge (perm y) (perm x))
  incoming_iff : ∀ {x y}, y ∉ P →
    (qEdge x y ↔ sEdge x (perm y))

namespace GroupedRotationData

variable {qEdge sEdge : Vertex → Vertex → Prop}
  {P I : Finset Vertex}
  (R : GroupedRotationData qEdge sEdge P I)

/-- Rotation of a finite vertex support. -/
def mapSupport (S : Finset Vertex) : Finset Vertex :=
  R.perm.finsetCongr S

/-- Rotation of a finite family of supports. -/
def mapFamily (C : Finset (Finset Vertex)) : Finset (Finset Vertex) :=
  R.perm.finsetCongr.finsetCongr C

omit [Fintype Vertex] [DecidableEq Vertex] in
@[simp]
theorem mem_mapSupport {S : Finset Vertex} {x : Vertex} :
    x ∈ R.mapSupport S ↔ R.perm.symm x ∈ S := by
  simp [mapSupport, Equiv.finsetCongr_apply]

omit [Fintype Vertex] [DecidableEq Vertex] in
@[simp]
theorem mapSupport_card (S : Finset Vertex) :
    (R.mapSupport S).card = S.card := by
  simp [mapSupport, Equiv.finsetCongr_apply]

/-- Reverse a grouped rotation. -/
def symm : GroupedRotationData sEdge qEdge I P where
  perm := R.perm.symm
  nonboundary_iff := by
    intro x
    simpa using (R.nonboundary_iff (R.perm.symm x)).symm
  edge_iff := by
    intro x y hx hy
    have hx' : R.perm.symm x ∉ P :=
      (R.nonboundary_iff (R.perm.symm x)).2 (by simpa using hx)
    have hy' : R.perm.symm y ∉ P :=
      (R.nonboundary_iff (R.perm.symm y)).2 (by simpa using hy)
    simpa using
      (R.edge_iff hy' hx').symm
  incoming_iff := by
    intro x y hy
    have hy' : R.perm.symm y ∉ P :=
      (R.nonboundary_iff (R.perm.symm y)).2 (by simpa using hy)
    simpa using
      (R.incoming_iff (x := x) hy').symm

omit [Fintype Vertex] [DecidableEq Vertex] in
@[simp]
theorem symm_mapSupport_mapSupport (S : Finset Vertex) :
    R.symm.mapSupport (R.mapSupport S) = S := by
  change R.perm.finsetCongr.symm (R.perm.finsetCongr S) = S
  exact R.perm.finsetCongr.symm_apply_apply S

omit [Fintype Vertex] [DecidableEq Vertex] in
@[simp]
theorem symm_mapFamily_mapFamily (C : Finset (Finset Vertex)) :
    R.symm.mapFamily (R.mapFamily C) = C := by
  change R.perm.finsetCongr.finsetCongr.symm
      (R.perm.finsetCongr.finsetCongr C) = C
  exact R.perm.finsetCongr.finsetCongr.symm_apply_apply C

omit [Fintype Vertex] [DecidableEq Vertex] in
/-- An internal path rotates to a path in the opposite direction. -/
theorem reachInside_map_reverse
    {S : Finset Vertex}
    (hS : ∀ x ∈ S, x ∉ P)
    {x y : Vertex}
    (hxy : ReachInside qEdge S x y) :
    ReachInside sEdge (R.mapSupport S) (R.perm y) (R.perm x) := by
  have hmap :
      Relation.ReflTransGen
          (fun a b : Vertex ↦
            InsideEdge sEdge (R.mapSupport S) b a)
          (R.perm x) (R.perm y) := by
    apply hxy.lift R.perm
    intro a b hab
    exact
      ⟨by simpa using hab.2.1,
        by simpa using hab.1,
        (R.edge_iff (hS a hab.1) (hS b hab.2.1)).1 hab.2.2⟩
  exact Relation.ReflTransGen.swap _ _ hmap

omit [Fintype Vertex] [DecidableEq Vertex] in
/-- Rotation sends strongly connected nonboundary supports to strongly
connected supports for the target relation. -/
theorem isStronglyConnectedInside_mapSupport
    {S : Finset Vertex}
    (hSboundary : ∀ x ∈ S, x ∉ P)
    (hS : IsStronglyConnectedInside qEdge S) :
    IsStronglyConnectedInside sEdge (R.mapSupport S) := by
  intro x hx y hy
  let x₀ := R.perm.symm x
  let y₀ := R.perm.symm y
  have hx₀ : x₀ ∈ S := by simpa [x₀] using hx
  have hy₀ : y₀ ∈ S := by simpa [y₀] using hy
  simpa [x₀, y₀] using
    R.reachInside_map_reverse hSboundary
      (hS y₀ hy₀ x₀ hx₀)

/-- Rotation preserves the strongly connected nonboundary candidate
supports. -/
theorem mem_minimalTopPartCandidates_mapSupport
    {S : Finset Vertex}
    (hS : S ∈ minimalTopPartCandidates qEdge P) :
    R.mapSupport S ∈ minimalTopPartCandidates sEdge I := by
  have hSdata := (mem_minimalTopPartCandidates.mp hS)
  have hScandidate := (mem_topPartCandidates.mp hSdata.1)
  apply mem_minimalTopPartCandidates.mpr
  constructor
  · apply mem_topPartCandidates.mpr
    constructor
    · simpa [mapSupport, Equiv.finsetCongr_apply] using hScandidate.1
    · intro x hx
      let x₀ := R.perm.symm x
      have hx₀ : x₀ ∈ S := by simpa [x₀] using hx
      simpa [x₀] using
        (R.nonboundary_iff x₀).1 (hScandidate.2 x₀ hx₀)
  · exact R.isStronglyConnectedInside_mapSupport hScandidate.2 hSdata.2

theorem mem_minimalTopPartCandidates_mapSupport_iff
    {S : Finset Vertex} :
    R.mapSupport S ∈ minimalTopPartCandidates sEdge I ↔
      S ∈ minimalTopPartCandidates qEdge P := by
  constructor
  · intro hS
    have hback := R.symm.mem_minimalTopPartCandidates_mapSupport hS
    simpa using hback
  · exact R.mem_minimalTopPartCandidates_mapSupport

/-- Rotation preserves separated support families whose members avoid the
source boundary. -/
theorem isSeparatedSupportFamily_mapFamily
    {C : Finset (Finset Vertex)}
    (hCandidates : ∀ S ∈ C,
      S ∈ minimalTopPartCandidates qEdge P)
    (hC : IsSeparatedSupportFamily qEdge C) :
    IsSeparatedSupportFamily sEdge (R.mapFamily C) := by
  have hmem : ∀ {T : Finset Vertex}, T ∈ R.mapFamily C →
      ∃ S ∈ C, R.mapSupport S = T := by
    intro T hT
    refine ⟨R.perm.finsetCongr.symm T, ?_, ?_⟩
    · simpa [mapFamily, Equiv.finsetCongr_apply] using hT
    · exact R.perm.finsetCongr.apply_symm_apply T
  constructor
  · constructor
    · intro T hT
      obtain ⟨S, hSC, rfl⟩ := hmem hT
      simpa [mapSupport, Equiv.finsetCongr_apply] using hC.1.1 S hSC
    · intro S hSC T hTC hST
      obtain ⟨S₀, hS₀C, rfl⟩ := hmem hSC
      obtain ⟨T₀, hT₀C, rfl⟩ := hmem hTC
      have hS₀T₀ : S₀ ≠ T₀ := by
        intro h
        exact hST (congrArg R.mapSupport h)
      rw [Finset.disjoint_left]
      intro x hx hy
      have hx₀ : R.perm.symm x ∈ S₀ := by simpa using hx
      have hy₀ : R.perm.symm x ∈ T₀ := by simpa using hy
      exact
        (Finset.disjoint_left.mp
          (hC.1.2 S₀ hS₀C T₀ hT₀C hS₀T₀)) hx₀ hy₀
  · intro S hSC T hTC hST x hx y hy hxy
    obtain ⟨S₀, hS₀C, rfl⟩ := hmem hSC
    obtain ⟨T₀, hT₀C, rfl⟩ := hmem hTC
    have hS₀T₀ : S₀ ≠ T₀ := by
      intro h
      exact hST (congrArg R.mapSupport h)
    have hx₀ : R.perm.symm x ∈ S₀ := by simpa using hx
    have hy₀ : R.perm.symm y ∈ T₀ := by simpa using hy
    have hxP :=
      (mem_topPartCandidates.mp
        (mem_minimalTopPartCandidates.mp
          (hCandidates S₀ hS₀C)).1).2 _ hx₀
    have hyP :=
      (mem_topPartCandidates.mp
        (mem_minimalTopPartCandidates.mp
          (hCandidates T₀ hT₀C)).1).2 _ hy₀
    exact hC.2 T₀ hT₀C S₀ hS₀C hS₀T₀.symm
      _ hy₀ _ hx₀ ((R.edge_iff hyP hxP).2 (by simpa using hxy))

/-- Rotation identifies the two finite types of separated minimal-candidate
families. -/
def separatedMinimalTopPartFamilyEquiv :
    SeparatedMinimalTopPartFamily qEdge P ≃
      SeparatedMinimalTopPartFamily sEdge I := by
  let eFamily := R.perm.finsetCongr.finsetCongr
  apply eFamily.subtypeEquiv
  intro C
  constructor
  · intro hC
    have hCdata := mem_separatedMinimalTopPartFamilies.mp hC
    apply mem_separatedMinimalTopPartFamilies.mpr
    refine ⟨?_, ?_, ?_⟩
    · intro T hT
      obtain ⟨S, hSC, rfl⟩ :
          ∃ S ∈ C, R.mapSupport S = T := by
        refine ⟨R.perm.finsetCongr.symm T, ?_, ?_⟩
        · simpa [eFamily, Equiv.finsetCongr_apply] using hT
        · exact R.perm.finsetCongr.apply_symm_apply T
      exact R.mem_minimalTopPartCandidates_mapSupport (hCdata.1 hSC)
    · simpa [eFamily, mapFamily, Equiv.finsetCongr_apply] using hCdata.2.1
    · exact R.isSeparatedSupportFamily_mapFamily hCdata.1 hCdata.2.2
  · intro hC
    have hback :
        R.symm.mapFamily (eFamily C) ∈
          separatedMinimalTopPartFamilies qEdge P := by
      have hCdata := mem_separatedMinimalTopPartFamilies.mp hC
      apply mem_separatedMinimalTopPartFamilies.mpr
      refine ⟨?_, ?_, ?_⟩
      · intro T hT
        obtain ⟨S, hSC, rfl⟩ :
            ∃ S ∈ eFamily C, R.symm.mapSupport S = T := by
          refine ⟨R.symm.perm.finsetCongr.symm T, ?_, ?_⟩
          · simpa [eFamily, mapFamily, symm,
              Equiv.finsetCongr_apply] using hT
          · exact R.symm.perm.finsetCongr.apply_symm_apply T
        exact R.symm.mem_minimalTopPartCandidates_mapSupport
          (hCdata.1 hSC)
      · simpa [eFamily, mapFamily, Equiv.finsetCongr_apply] using hCdata.2.1
      · exact R.symm.isSeparatedSupportFamily_mapFamily
          hCdata.1 hCdata.2.2
    change R.symm.mapFamily (R.mapFamily C) ∈
      separatedMinimalTopPartFamilies qEdge P at hback
    simpa using hback

omit [Fintype Vertex] in
/-- Rotation commutes with taking the union of a support family. -/
theorem mapSupport_supportFamilyUnion
    (C : Finset (Finset Vertex)) :
    R.mapSupport (supportFamilyUnion C) =
      supportFamilyUnion (R.mapFamily C) := by
  ext x
  constructor
  · intro hx
    have hx' : R.perm.symm x ∈ supportFamilyUnion C := by simpa using hx
    obtain ⟨S, hSC, hxS⟩ := Finset.mem_biUnion.mp hx'
    apply Finset.mem_biUnion.mpr
    refine ⟨R.mapSupport S, ?_, by simpa⟩
    rw [mapFamily, Equiv.finsetCongr_apply]
    apply Finset.mem_map.mpr
    exact ⟨S, hSC, by simp [mapSupport, Equiv.finsetCongr_apply]⟩
  · intro hx
    obtain ⟨T, hTC, hxT⟩ := Finset.mem_biUnion.mp hx
    let S := R.perm.finsetCongr.symm T
    have hSC : S ∈ C := by
      simpa [S, mapFamily, Equiv.finsetCongr_apply] using hTC
    have hST : R.mapSupport S = T := by
      exact R.perm.finsetCongr.apply_symm_apply T
    apply (mem_mapSupport (R := R)).2
    apply Finset.mem_biUnion.mpr
    refine ⟨S, hSC, ?_⟩
    apply (mem_mapSupport (R := R)).1
    change x ∈ R.mapSupport S
    rw [hST]
    exact hxT

/-- In a separated family of strongly connected supports, a vertex has an
internal outgoing edge exactly when it has an internal incoming edge. -/
theorem exists_outgoing_iff_exists_incoming_supportFamilyUnion
    {C : Finset (Finset Vertex)}
    (hCandidates : ∀ S ∈ C,
      S ∈ minimalTopPartCandidates qEdge P)
    (hSeparated : IsSeparatedSupportFamily qEdge C)
    {x : Vertex} (hx : x ∈ supportFamilyUnion C) :
    (∃ y ∈ supportFamilyUnion C, qEdge x y) ↔
      ∃ y ∈ supportFamilyUnion C, qEdge y x := by
  obtain ⟨S, hSC, hxS⟩ := Finset.mem_biUnion.mp hx
  have hSstrong :=
    (mem_minimalTopPartCandidates.mp (hCandidates S hSC)).2
  constructor
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨T, hTC, hyT⟩ := Finset.mem_biUnion.mp hy
    have hST : S = T := by
      by_contra hne
      exact hSeparated.2 S hSC T hTC hne x hxS y hyT hxy
    subst T
    rcases Relation.ReflTransGen.cases_tail
        (hSstrong y hyT x hxS) with h | ⟨z, hyz, hzx⟩
    · subst y
      exact ⟨x, hx, hxy⟩
    · exact
        ⟨z,
          Finset.mem_biUnion.mpr ⟨S, hSC, hzx.1⟩,
          hzx.2.2⟩
  · rintro ⟨y, hy, hyx⟩
    obtain ⟨T, hTC, hyT⟩ := Finset.mem_biUnion.mp hy
    have hST : S = T := by
      by_contra hne
      exact hSeparated.2 T hTC S hSC (Ne.symm hne) y hyT x hxS hyx
    subst T
    rcases Relation.ReflTransGen.cases_head
        (hSstrong x hxS y hyT) with h | ⟨z, hxz, hzy⟩
    · subst y
      exact ⟨x, hx, hyx⟩
    · exact
        ⟨z,
          Finset.mem_biUnion.mpr ⟨S, hSC, hxz.2.1⟩,
          hxz.2.2⟩

/-- Mesh rotation identifies the predecessor region of a support union with
the predecessor region of its rotated union in the target graph. -/
theorem immediatePredecessors_supportFamilyUnion_eq
    {C : Finset (Finset Vertex)}
    (hCandidates : ∀ S ∈ C,
      S ∈ minimalTopPartCandidates qEdge P) :
    immediatePredecessors qEdge (supportFamilyUnion C) =
      immediatePredecessors sEdge
        (supportFamilyUnion (R.mapFamily C)) := by
  have hboundary : ∀ y ∈ supportFamilyUnion C, y ∉ P := by
    intro y hy
    obtain ⟨S, hSC, hyS⟩ := Finset.mem_biUnion.mp hy
    exact
      (mem_topPartCandidates.mp
        (mem_minimalTopPartCandidates.mp
          (hCandidates S hSC)).1).2 y hyS
  rw [← R.mapSupport_supportFamilyUnion]
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, hxy⟩ := mem_immediatePredecessors.mp hx
    apply mem_immediatePredecessors.mpr
    refine ⟨R.perm y, by simpa, ?_⟩
    exact (R.incoming_iff (hboundary y hy)).1 hxy
  · intro hx
    obtain ⟨z, hz, hxz⟩ := mem_immediatePredecessors.mp hx
    let y := R.perm.symm z
    have hy : y ∈ supportFamilyUnion C := by simpa [y] using hz
    apply mem_immediatePredecessors.mpr
    refine ⟨y, hy, ?_⟩
    have hzy : R.perm y = z := by simp [y]
    rw [← hzy] at hxz
    exact (R.incoming_iff (hboundary y hy)).2 hxz

/-- A support vertex belongs to the common forced predecessor region exactly
when its rotated vertex does. -/
theorem mem_immediatePredecessors_iff_perm_mem
    {C : Finset (Finset Vertex)}
    (hCandidates : ∀ S ∈ C,
      S ∈ minimalTopPartCandidates qEdge P)
    (hSeparated : IsSeparatedSupportFamily qEdge C)
    {x : Vertex} (hx : x ∈ supportFamilyUnion C) :
    x ∈ immediatePredecessors qEdge (supportFamilyUnion C) ↔
      R.perm x ∈ immediatePredecessors qEdge
        (supportFamilyUnion C) := by
  let W := supportFamilyUnion C
  let WT := supportFamilyUnion (R.mapFamily C)
  have hpred : immediatePredecessors qEdge W =
      immediatePredecessors sEdge WT :=
    R.immediatePredecessors_supportFamilyUnion_eq hCandidates
  constructor
  · intro hxpred
    have hout : ∃ y ∈ W, qEdge x y :=
      mem_immediatePredecessors.mp hxpred
    have hin : ∃ y ∈ W, qEdge y x :=
      (exists_outgoing_iff_exists_incoming_supportFamilyUnion
        (qEdge := qEdge) (P := P) hCandidates hSeparated hx).1 hout
    obtain ⟨y, hy, hyx⟩ := hin
    rw [hpred]
    apply mem_immediatePredecessors.mpr
    refine ⟨R.perm y, ?_, ?_⟩
    · change R.perm y ∈ supportFamilyUnion (R.mapFamily C)
      rw [← R.mapSupport_supportFamilyUnion]
      simpa
    · have hyP :=
        (mem_topPartCandidates.mp
          (mem_minimalTopPartCandidates.mp
            (hCandidates _ (Finset.mem_biUnion.mp hy).choose_spec.1)).1).2
          y (Finset.mem_biUnion.mp hy).choose_spec.2
      exact (R.edge_iff hyP <|
        (mem_topPartCandidates.mp
          (mem_minimalTopPartCandidates.mp
            (hCandidates _ (Finset.mem_biUnion.mp hx).choose_spec.1)).1).2
          x (Finset.mem_biUnion.mp hx).choose_spec.2).1 hyx
  · intro hxpred
    rw [hpred] at hxpred
    obtain ⟨z, hz, hzx⟩ := mem_immediatePredecessors.mp hxpred
    change z ∈ supportFamilyUnion (R.mapFamily C) at hz
    rw [← R.mapSupport_supportFamilyUnion] at hz
    let y := R.perm.symm z
    have hy : y ∈ W := by simpa [y] using hz
    have hyP :=
      (mem_topPartCandidates.mp
        (mem_minimalTopPartCandidates.mp
          (hCandidates _ (Finset.mem_biUnion.mp hy).choose_spec.1)).1).2
        y (Finset.mem_biUnion.mp hy).choose_spec.2
    have hxP :=
      (mem_topPartCandidates.mp
        (mem_minimalTopPartCandidates.mp
          (hCandidates _ (Finset.mem_biUnion.mp hx).choose_spec.1)).1).2
        x (Finset.mem_biUnion.mp hx).choose_spec.2
    have hyx : qEdge y x := by
      apply (R.edge_iff hyP hxP).2
      simpa [y] using hzx
    have hin : ∃ y ∈ W, qEdge y x := ⟨y, hy, hyx⟩
    have hout : ∃ y ∈ W, qEdge x y :=
      (exists_outgoing_iff_exists_incoming_supportFamilyUnion
        (qEdge := qEdge) (P := P) hCandidates hSeparated hx).2 hin
    exact mem_immediatePredecessors.mpr hout

/-- Rotation preserves the cardinality of the forced region attached to a
separated strongly connected support family. -/
theorem topPartForcedRegion_card_eq
    {C : Finset (Finset Vertex)}
    (hCandidates : ∀ S ∈ C,
      S ∈ minimalTopPartCandidates qEdge P)
    (hSeparated : IsSeparatedSupportFamily qEdge C) :
    (topPartForcedRegion qEdge (supportFamilyUnion C)).card =
      (topPartForcedRegion sEdge
        (supportFamilyUnion (R.mapFamily C))).card := by
  let W := supportFamilyUnion C
  let WT := supportFamilyUnion (R.mapFamily C)
  let A := immediatePredecessors qEdge W
  have hpred : immediatePredecessors sEdge WT = A :=
    (R.immediatePredecessors_supportFamilyUnion_eq hCandidates).symm
  have hsdiff : R.mapSupport (W \ A) = WT \ A := by
    ext x
    let y := R.perm.symm x
    constructor
    · intro hxdata
      have hydata : y ∈ W \ A := by simpa [y] using hxdata
      have hyW := (Finset.mem_sdiff.mp hydata).1
      have hyA := (Finset.mem_sdiff.mp hydata).2
      apply Finset.mem_sdiff.mpr
      constructor
      · change x ∈ supportFamilyUnion (R.mapFamily C)
        rw [← R.mapSupport_supportFamilyUnion]
        simpa [y]
      · intro hxA
        have hA := R.mem_immediatePredecessors_iff_perm_mem
          hCandidates hSeparated hyW
        apply hyA
        have hey : R.perm y = x := by simp [y]
        rw [hey] at hA
        exact hA.mpr hxA
    · intro hxdata
      have hxWT := (Finset.mem_sdiff.mp hxdata).1
      have hxA := (Finset.mem_sdiff.mp hxdata).2
      have hyW : y ∈ W := by
        change x ∈ supportFamilyUnion (R.mapFamily C) at hxWT
        rw [← R.mapSupport_supportFamilyUnion] at hxWT
        simpa [y] using hxWT
      apply (mem_mapSupport (R := R)).2
      apply Finset.mem_sdiff.mpr
      refine ⟨hyW, ?_⟩
      intro hyA
      apply hxA
      have hA := R.mem_immediatePredecessors_iff_perm_mem
        hCandidates hSeparated hyW
      have hyA' := hA.mp hyA
      have hey : R.perm y = x := by simp [y]
      rw [hey] at hyA'
      exact hyA'
  unfold topPartForcedRegion
  change (W ∪ A).card = (WT ∪ immediatePredecessors sEdge WT).card
  rw [hpred, ← Finset.card_sdiff_add_card W A,
    ← Finset.card_sdiff_add_card WT A]
  rw [← hsdiff]
  simp

/-- Equivalence between the grouped support-union index types. -/
def separatedSupportUnionEquiv :
    Set.range (separatedMinimalTopPartFamilyUnion qEdge P) ≃
      Set.range (separatedMinimalTopPartFamilyUnion sEdge I) :=
  (separatedMinimalTopPartFamilyUnionEquiv qEdge P).symm.trans <|
    R.separatedMinimalTopPartFamilyEquiv.trans <|
      separatedMinimalTopPartFamilyUnionEquiv sEdge I

/-- The graph-theoretic mesh rotation supplies the complete grouped matching
used by rooted balance. -/
def groupedTopPartMatching :
    GroupedTopPartMatching qEdge sEdge P I where
  equiv := R.separatedSupportUnionEquiv
  componentCount_eq := by
    intro W
    unfold separatedSupportUnionComponentCount
    simp [separatedSupportUnionEquiv,
      separatedMinimalTopPartFamilyEquiv]
  supportCard_eq := by
    intro W
    let C := (separatedMinimalTopPartFamilyUnionEquiv qEdge P).symm W
    change W.1.card = (R.separatedSupportUnionEquiv W).1.card
    have hW : W.1 = supportFamilyUnion C.1 := by
      change W.1 =
        ((separatedMinimalTopPartFamilyUnionEquiv qEdge P) C).1
      exact congrArg Subtype.val
        ((separatedMinimalTopPartFamilyUnionEquiv qEdge P).apply_symm_apply W).symm
    have htarget : (R.separatedSupportUnionEquiv W).1 =
        supportFamilyUnion
          (R.mapFamily C.1) := by
      change separatedMinimalTopPartFamilyUnion sEdge I
          (R.separatedMinimalTopPartFamilyEquiv C) =
        supportFamilyUnion (R.mapFamily C.1)
      rfl
    rw [hW, htarget, ← R.mapSupport_supportFamilyUnion]
    simp
  forcedRegionCard_eq := by
    intro W
    let C := (separatedMinimalTopPartFamilyUnionEquiv qEdge P).symm W
    have hCdata := mem_separatedMinimalTopPartFamilies.mp C.2
    have hW : W.1 = supportFamilyUnion C.1 := by
      change W.1 =
        ((separatedMinimalTopPartFamilyUnionEquiv qEdge P) C).1
      exact congrArg Subtype.val
        ((separatedMinimalTopPartFamilyUnionEquiv qEdge P).apply_symm_apply W).symm
    have htarget : (R.separatedSupportUnionEquiv W).1 =
        supportFamilyUnion (R.mapFamily C.1) := by
      change separatedMinimalTopPartFamilyUnion sEdge I
          (R.separatedMinimalTopPartFamilyEquiv C) =
        supportFamilyUnion (R.mapFamily C.1)
      rfl
    rw [hW, htarget]
    exact R.topPartForcedRegion_card_eq hCdata.1 hCdata.2.2

end GroupedRotationData

end QuotientSubmoduleEquidistribution.RootedDigraph
