import OpConjecture.RepresentationTheory.FourVertexDiagonalM4RegularCuts
import OpConjecture.RepresentationTheory.FourVertexDualArrowOccurrences

/-!
# Aligned reversal of diagonal arrow-chain cuts

Aligned biduality reverses every maximal labelled arrow chain, preserves its
length, and reflects its vertex position `e` to `L - e`. This file packages
that chain equivalence and proves that aggregate last diagonal cuts on one
skeleton are exactly the first diagonal cuts on the aligned dual skeleton.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace OpConjecture.IndecomposableSkeleton

universe u v w

variable {R S : Type u}
  [Ring R] [IsNoetherianRing R]
  [Ring S] [IsNoetherianRing S]
  {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)
  (τ : IndecomposableSkeleton.{u, w, u} S κ)

namespace AlignedBiduality

variable (D : AlignedBiduality σ τ)

omit [Fintype ι] [Fintype κ] in
/-- Pullback for the swapped biduality is the original pushforward on
labelled irreducible arrows. -/
theorem swap_pullbackIrreduciblePair_eq_pushforward
    (a : σ.IrreduciblePair) :
    (D.swap σ τ).pullbackIrreduciblePair τ σ a =
      D.pushforwardIrreduciblePair σ τ a := by
  apply Subtype.ext
  apply Prod.ext
  · change D.backward.labelEquiv.symm a.1.2 =
      D.forward.labelEquiv a.1.2
    simp [D.backward_label]
  · change D.backward.labelEquiv.symm a.1.1 =
      D.forward.labelEquiv a.1.1
    simp [D.backward_label]

/-- Arrow reversal identifies injective-source occurrences on the source
skeleton with projective-target occurrences on the aligned dual. -/
def injectiveSourceIrreduciblePairEquivProjectiveTarget :
    {a : σ.IrreduciblePair // Injective (σ.obj a.1.1)} ≃
      {a : τ.IrreduciblePair // Projective (τ.obj a.1.2)} where
  toFun a := ⟨D.pushforwardIrreduciblePair σ τ a.1, by
    simpa [pushforwardIrreduciblePair] using
      (D.forward.injective_iff_projective_image σ τ a.1.1.1).1 a.2⟩
  invFun a := ⟨D.pullbackIrreduciblePair σ τ a.1, by
    have h := (D.forward.injective_iff_projective_image σ τ
      (D.forward.labelEquiv.symm a.1.1.2)).2 (by
        simpa using a.2)
    simpa [pullbackIrreduciblePair] using h⟩
  left_inv a := by
    apply Subtype.ext
    exact (D.irreduciblePairEquiv σ τ).apply_symm_apply a.1
  right_inv a := by
    apply Subtype.ext
    exact (D.irreduciblePairEquiv σ τ).symm_apply_apply a.1

end AlignedBiduality

namespace FiniteARTranslationData

variable (ARσ : σ.FiniteARTranslationData)
  (ARτ : τ.FiniteARTranslationData)
  (D : AlignedBiduality σ τ)

/-- Pushing forward one source mesh rotation is one inverse mesh rotation
on the aligned dual arrow occurrence. -/
theorem pushforward_arrowOrbit_tau
    (a : {a : σ.IrreduciblePair //
      ¬ Projective (σ.obj a.1.2)}) :
    D.pushforwardIrreduciblePair σ τ
        (((ARσ.arMeshRotationData σ).arrowOrbitData σ).tau a).1 =
      (((ARτ.arMeshRotationData τ).arrowOrbitData τ).tau.symm
        ⟨D.pushforwardIrreduciblePair σ τ a.1,
          D.pushforwardIrreduciblePair_source_noninjective
            σ τ a.1 a.2⟩).1 := by
  let D' := D.swap σ τ
  have h := D'.pullback_arrowOrbit_tau τ σ ARτ ARσ a
  simpa only [D', D.swap_pullbackIrreduciblePair_eq_pushforward σ τ] using h

/-- Arrow reversal conjugates reversed source mesh successor to ordinary
dual mesh successor. -/
theorem pushforward_arrowOrbit_reverse_successor
    [DecidableEq ι] [DecidableEq κ]
    (a : σ.IrreduciblePair) :
    D.pushforwardIrreduciblePair σ τ
        ((ARσ.arMeshRotationData σ).arrowOrbitData σ |>.reverse.successor a) =
      ((ARτ.arMeshRotationData τ).arrowOrbitData τ).successor
        (D.pushforwardIrreduciblePair σ τ a) := by
  let Oσ := (ARσ.arMeshRotationData σ).arrowOrbitData σ
  let Oτ := (ARτ.arMeshRotationData τ).arrowOrbitData τ
  by_cases hp : Projective (σ.obj a.1.2)
  · have hi : Injective
        (τ.obj (D.pushforwardIrreduciblePair σ τ a).1.1) := by
      simpa [AlignedBiduality.pushforwardIrreduciblePair] using
        (D.forward.projective_iff_injective_image σ τ a.1.2).1 hp
    rw [Oσ.reverse.successor_eq_self_of_mem_target hp,
      Oτ.successor_eq_self_of_mem_target hi]
  · have hni : ¬ Injective
        (τ.obj (D.pushforwardIrreduciblePair σ τ a).1.1) :=
      D.pushforwardIrreduciblePair_source_noninjective σ τ a hp
    have hσ : Oσ.reverse.successor a = (Oσ.tau ⟨a, hp⟩).1 := by
      simp [OpConjecture.BoundaryTranslationChains.Data.successor,
        OpConjecture.BoundaryTranslationChains.Data.reverse, hp]
    have hτ : Oτ.successor (D.pushforwardIrreduciblePair σ τ a) =
        (Oτ.tau.symm
          ⟨D.pushforwardIrreduciblePair σ τ a, hni⟩).1 := by
      simp [OpConjecture.BoundaryTranslationChains.Data.successor, hni]
    rw [hσ, hτ]
    exact pushforward_arrowOrbit_tau σ τ ARσ ARτ D ⟨a, hp⟩

/-- The preceding conjugacy holds for every number of reversed chain
steps. -/
theorem pushforward_arrowOrbit_reverse_iterate
    [DecidableEq ι] [DecidableEq κ]
    (a : σ.IrreduciblePair) (n : ℕ) :
    D.pushforwardIrreduciblePair σ τ
        ((((ARσ.arMeshRotationData σ).arrowOrbitData σ).reverse.successor^[n])
          a) =
      (((ARτ.arMeshRotationData τ).arrowOrbitData τ).successor^[n])
        (D.pushforwardIrreduciblePair σ τ a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
      exact pushforward_arrowOrbit_reverse_successor σ τ ARσ ARτ D _

/-- Canonically reverse a maximal projective-to-injective arrow chain into
the projective-starting chain on the aligned dual skeleton. -/
def dualProjectiveTargetArrowEquiv [DecidableEq ι] [DecidableEq κ] :
    {a : σ.IrreduciblePair // Projective (σ.obj a.1.2)} ≃
      {a : τ.IrreduciblePair // Projective (τ.obj a.1.2)} :=
  (((ARσ.arMeshRotationData σ).arrowOrbitData σ).boundaryEndpointEquiv).trans
    (D.injectiveSourceIrreduciblePairEquivProjectiveTarget σ τ)

omit [Fintype κ] in
/-- Pulling the dual start back recovers the terminal occurrence of the
source chain. -/
theorem pullback_dualProjectiveTargetArrowEquiv_apply
    [DecidableEq ι] [DecidableEq κ]
    (a : {a : σ.IrreduciblePair // Projective (σ.obj a.1.2)}) :
    D.pullbackIrreduciblePair σ τ
        (dualProjectiveTargetArrowEquiv σ τ ARσ D a).1 =
      (ARσ.arMeshRotationData σ).arrowChainAt σ a.1
        ((ARσ.arMeshRotationData σ).arrowChainLength σ a.1 a.2) := by
  let O := (ARσ.arMeshRotationData σ).arrowOrbitData σ
  have h := (D.irreduciblePairEquiv σ τ).apply_symm_apply
    (O.boundaryEndpointEquiv a).1
  exact h

omit [Fintype κ] in
/-- The dual start is literally the reversed terminal source occurrence. -/
theorem dualProjectiveTargetArrowEquiv_apply
    [DecidableEq ι] [DecidableEq κ]
    (a : {a : σ.IrreduciblePair // Projective (σ.obj a.1.2)}) :
    (dualProjectiveTargetArrowEquiv σ τ ARσ D a).1 =
      D.pushforwardIrreduciblePair σ τ
        ((ARσ.arMeshRotationData σ).arrowChainAt σ a.1
          ((ARσ.arMeshRotationData σ).arrowChainLength σ a.1 a.2)) := by
  let b := dualProjectiveTargetArrowEquiv σ τ ARσ D a
  have hpull := pullback_dualProjectiveTargetArrowEquiv_apply
    σ τ ARσ D a
  calc
    b.1 = D.pushforwardIrreduciblePair σ τ
        (D.pullbackIrreduciblePair σ τ b.1) :=
      (D.irreduciblePairEquiv σ τ).symm_apply_apply b.1 |>.symm
    _ = D.pushforwardIrreduciblePair σ τ
        ((ARσ.arMeshRotationData σ).arrowChainAt σ a.1
          ((ARσ.arMeshRotationData σ).arrowChainLength σ a.1 a.2)) :=
      congrArg _ hpull

/-- At every position up to the endpoint, the dual chain is the labelled
arrow reversal of the source chain at the complementary position. -/
theorem dualArrowChainAt_eq_pushforward
    [DecidableEq ι] [DecidableEq κ]
    (a : {a : σ.IrreduciblePair // Projective (σ.obj a.1.2)})
    {n : ℕ}
    (hn : n ≤ (ARσ.arMeshRotationData σ).arrowChainLength σ a.1 a.2) :
    let b := dualProjectiveTargetArrowEquiv σ τ ARσ D a
    (ARτ.arMeshRotationData τ).arrowChainAt τ b.1 n =
      D.pushforwardIrreduciblePair σ τ
        ((ARσ.arMeshRotationData σ).arrowChainAt σ a.1
          ((ARσ.arMeshRotationData σ).arrowChainLength σ a.1 a.2 - n)) := by
  let Mσ := ARσ.arMeshRotationData σ
  let Mτ := ARτ.arMeshRotationData τ
  let Oσ := Mσ.arrowOrbitData σ
  let Oτ := Mτ.arrowOrbitData τ
  let b := dualProjectiveTargetArrowEquiv σ τ ARσ D a
  let N := Mσ.arrowChainLength σ a.1 a.2
  let z := Mσ.arrowChainAt σ a.1 N
  have hpull : D.pullbackIrreduciblePair σ τ b.1 = z := by
    exact pullback_dualProjectiveTargetArrowEquiv_apply σ τ ARσ D a
  have hstart : b.1 = D.pushforwardIrreduciblePair σ τ z := by
    calc
      b.1 = D.pushforwardIrreduciblePair σ τ
          (D.pullbackIrreduciblePair σ τ b.1) :=
        (D.irreduciblePairEquiv σ τ).symm_apply_apply b.1 |>.symm
      _ = D.pushforwardIrreduciblePair σ τ z := congrArg _ hpull
  change (Oτ.successor^[n]) b.1 =
    D.pushforwardIrreduciblePair σ τ (Mσ.arrowChainAt σ a.1 (N - n))
  calc
    (Oτ.successor^[n]) b.1 =
        (Oτ.successor^[n]) (D.pushforwardIrreduciblePair σ τ z) :=
      congrArg (Oτ.successor^[n]) hstart
    _ = D.pushforwardIrreduciblePair σ τ
          ((Oσ.reverse.successor^[n]) z) :=
      (pushforward_arrowOrbit_reverse_iterate σ τ ARσ ARτ D z n).symm
    _ = D.pushforwardIrreduciblePair σ τ
          (Mσ.arrowChainAt σ a.1 (N - n)) := by
      congr 1
      exact Mσ.arrowChain_reverse_iterate_endpoint_eq σ a.1 a.2 hn

/-- Aligned reversal preserves the maximal labelled arrow-chain length. -/
theorem dualArrowChainLength_eq
    [DecidableEq ι] [DecidableEq κ]
    (a : {a : σ.IrreduciblePair // Projective (σ.obj a.1.2)}) :
    let b := dualProjectiveTargetArrowEquiv σ τ ARσ D a
    (ARτ.arMeshRotationData τ).arrowChainLength τ b.1 b.2 =
      (ARσ.arMeshRotationData σ).arrowChainLength σ a.1 a.2 := by
  classical
  let Mσ := ARσ.arMeshRotationData σ
  let Mτ := ARτ.arMeshRotationData τ
  let Oσ := Mσ.arrowOrbitData σ
  let Oτ := Mτ.arrowOrbitData τ
  let b := dualProjectiveTargetArrowEquiv σ τ ARσ D a
  let N := Mσ.arrowChainLength σ a.1 a.2
  change Oτ.firstTargetIndex b.1 b.2 = N
  apply Nat.le_antisymm
  · have hAt := dualArrowChainAt_eq_pushforward
      σ τ ARσ ARτ D a (n := N) le_rfl
    have hiPush : Injective
        (τ.obj (D.pushforwardIrreduciblePair σ τ a.1).1.1) := by
      simpa [AlignedBiduality.pushforwardIrreduciblePair] using
        (D.forward.projective_iff_injective_image σ τ a.1.1.2).1 a.2
    have hi : Injective (τ.obj (Mτ.arrowChainAt τ b.1 N).1.1) := by
      rw [hAt]
      simpa [N, Mσ, ARMeshRotationData.arrowChainAt] using hiPush
    exact Nat.find_min'
      (Oτ.exists_iterate_mem_target_unbounded b.1 b.2) hi
  · by_contra hnot
    have hrlt : Oτ.firstTargetIndex b.1 b.2 < N := by omega
    let r := Oτ.firstTargetIndex b.1 b.2
    have hAt := dualArrowChainAt_eq_pushforward
      σ τ ARσ ARτ D a (n := r) (Nat.le_of_lt hrlt)
    have hi := Oτ.firstTargetIndex_spec b.1 b.2
    have hiPush : Injective
        (τ.obj
          (D.pushforwardIrreduciblePair σ τ
            (Mσ.arrowChainAt σ a.1 (N - r))).1.1) := by
      rw [← hAt]
      exact hi
    have hp : Projective
        (σ.obj (Mσ.arrowChainAt σ a.1 (N - r)).1.2) := by
      apply (D.forward.projective_iff_injective_image σ τ _).2
      simpa [AlignedBiduality.pushforwardIrreduciblePair] using hiPush
    have hnotP : ¬ Projective
        (σ.obj (Mσ.arrowChainAt σ a.1 (N - r)).1.2) := by
      exact Oσ.iterate_not_mem_source_of_pos_le_firstTargetIndex
        a.1 a.2 (Nat.sub_pos_of_lt hrlt) (Nat.sub_le N r)
    exact hnotP hp

/-- The vertex list of the dual maximal chain is the labelwise reversal of
the source vertex list. -/
theorem dualArrowChainVertexNat_eq
    [DecidableEq ι] [DecidableEq κ]
    (a : {a : σ.IrreduciblePair // Projective (σ.obj a.1.2)})
    {e : ℕ}
    (he : e ≤
      (ARσ.arMeshRotationData σ).arrowChainLength σ a.1 a.2 + 1) :
    let b := dualProjectiveTargetArrowEquiv σ τ ARσ D a
    ARτ.arrowChainVertexNat τ b.1 b.2 e =
      D.forward.labelEquiv
        (ARσ.arrowChainVertexNat σ a.1 a.2
          ((ARσ.arMeshRotationData σ).arrowChainLength σ a.1 a.2 + 1 - e)) := by
  let Mσ := ARσ.arMeshRotationData σ
  let Mτ := ARτ.arMeshRotationData τ
  let b := dualProjectiveTargetArrowEquiv σ τ ARσ D a
  let N := Mσ.arrowChainLength σ a.1 a.2
  have hlen : Mτ.arrowChainLength τ b.1 b.2 = N :=
    dualArrowChainLength_eq σ τ ARσ ARτ D a
  change e ≤ N + 1 at he
  rcases e with _ | n
  · have hsource := ARτ.arrowChainAt_source_eq_vertexNat
      τ b.1 b.2 (n := 0) (by rw [hlen]; omega)
    have hstart := dualProjectiveTargetArrowEquiv_apply σ τ ARσ D a
    have htarget := ARσ.arrowChainAt_target_eq_vertexNat_succ
      σ a.1 a.2 (n := N) le_rfl
    calc
      ARτ.arrowChainVertexNat τ b.1 b.2 0 =
          (Mτ.arrowChainAt τ b.1 0).1.1 := hsource.symm
      _ = b.1.1.1 := by
        simp [ARMeshRotationData.arrowChainAt]
      _ = (D.pushforwardIrreduciblePair σ τ
          (Mσ.arrowChainAt σ a.1 N)).1.1 :=
        congrArg (fun q : τ.IrreduciblePair ↦ q.1.1) hstart
      _ = D.forward.labelEquiv
          (Mσ.arrowChainAt σ a.1 N).1.2 := rfl
      _ = D.forward.labelEquiv
          (ARσ.arrowChainVertexNat σ a.1 a.2 (N + 1 - 0)) := by
        rw [Nat.sub_zero]
        exact congrArg D.forward.labelEquiv htarget
  · have hn : n ≤ N := by omega
    have htarget := ARτ.arrowChainAt_target_eq_vertexNat_succ
      τ b.1 b.2 (n := n) (by rw [hlen]; exact hn)
    have hAt := dualArrowChainAt_eq_pushforward
      σ τ ARσ ARτ D a (n := n) hn
    have hsource := ARσ.arrowChainAt_source_eq_vertexNat
      σ a.1 a.2 (n := N - n) (Nat.sub_le N n)
    calc
      ARτ.arrowChainVertexNat τ b.1 b.2 (n + 1) =
          (Mτ.arrowChainAt τ b.1 n).1.2 := htarget.symm
      _ = (D.pushforwardIrreduciblePair σ τ
          (Mσ.arrowChainAt σ a.1 (N - n))).1.2 :=
        congrArg (fun q : τ.IrreduciblePair ↦ q.1.2) hAt
      _ = D.forward.labelEquiv
          (Mσ.arrowChainAt σ a.1 (N - n)).1.1 := rfl
      _ = D.forward.labelEquiv
          (ARσ.arrowChainVertexNat σ a.1 a.2 (N + 1 - (n + 1))) := by
        rw [show N + 1 - (n + 1) = N - n by omega]
        exact congrArg D.forward.labelEquiv hsource

/-- Aligned reversal equivalently matches the starts of all long maximal
arrow chains. -/
def dualLongArrowChainStartEquiv
    [DecidableEq ι] [DecidableEq κ] :
    ARσ.LongArrowChainStart σ ≃ ARτ.LongArrowChainStart τ := by
  let E := dualProjectiveTargetArrowEquiv σ τ ARσ D
  apply E.subtypeEquiv
  intro a
  rw [dualArrowChainLength_eq σ τ ARσ ARτ D a]

/-- Aligned reversal also matches exactly the maximal arrow chains of
length three which supply the short same-orbit boundary remainder. -/
def dualLengthThreeArrowChainStartEquiv
    [DecidableEq ι] [DecidableEq κ] :
    ARσ.LengthThreeArrowChainStart σ ≃
      ARτ.LengthThreeArrowChainStart τ := by
  let E := dualProjectiveTargetArrowEquiv σ τ ARσ D
  apply E.subtypeEquiv
  intro a
  rw [dualArrowChainLength_eq σ τ ARσ ARτ D a]

/-- Exact aligned reversal of the short diagonal same-orbit complements. -/
def longArrowChainFirstDiagonalFirstBoundarySameOrbitRemainderEquivAligned
    [DecidableEq ι] [DecidableEq κ] :
    ARσ.LongArrowChainFirstDiagonalFirstBoundarySameOrbitRemainder σ ≃
      ARτ.LongArrowChainFirstDiagonalFirstBoundarySameOrbitRemainder τ :=
  (ARσ.lengthThreeArrowChainStartEquivSameOrbitRemainder σ).symm |>.trans
    ((dualLengthThreeArrowChainStartEquiv σ τ ARσ ARτ D).trans
      (ARτ.lengthThreeArrowChainStartEquivSameOrbitRemainder τ))

include D in
/-- Cardinal invariance of the formerly implicit short same-orbit
contribution under aligned reversal. -/
theorem longArrowChainFirstDiagonalFirstBoundarySameOrbitRemainder_card_eq
    [DecidableEq ι] [DecidableEq κ] :
    Fintype.card
        (ARσ.LongArrowChainFirstDiagonalFirstBoundarySameOrbitRemainder σ) =
      Fintype.card
        (ARτ.LongArrowChainFirstDiagonalFirstBoundarySameOrbitRemainder τ) :=
  Fintype.card_congr
    (longArrowChainFirstDiagonalFirstBoundarySameOrbitRemainderEquivAligned
      σ τ ARσ ARτ D)

/-- Reflect a last cut on a source chain into the first cut of its aligned
dual reversed chain. -/
def longArrowChainLastDiagonalCutToDualFirst
    [DecidableEq ι] [DecidableEq κ]
    (q : ARσ.LongArrowChainLastDiagonalCut σ) :
    ARτ.LongArrowChainFirstDiagonalCut τ := by
  let a := q.1
  let a₀ := a.1
  let b₀ := dualProjectiveTargetArrowEquiv σ τ ARσ D a₀
  let Mσ := ARσ.arMeshRotationData σ
  let Mτ := ARτ.arMeshRotationData τ
  let N := Mσ.arrowChainLength σ a₀.1 a₀.2
  let e := q.2.1.1
  let d := N + 1 - e
  have hlen : Mτ.arrowChainLength τ b₀.1 b₀.2 = N := by
    exact dualArrowChainLength_eq σ τ ARσ ARτ D a₀
  have hN : 4 ≤ N := by
    simpa only [N, a₀, a] using a.2
  let b : ARτ.LongArrowChainStart τ := ⟨b₀, by
    rw [hlen]
    exact a.2⟩
  have heLower : 2 ≤ e := q.2.1.2.1
  have heUpper : e ≤ N + 1 - 2 := by
    simpa only [N, a₀, a] using q.2.1.2.2
  have hdLower : 2 ≤ d := by dsimp [d]; omega
  have hdUpper : d ≤ Mτ.arrowChainLength τ b₀.1 b₀.2 + 1 - 2 := by
    rw [hlen]
    dsimp [d]
    omega
  have htwoBound : 2 ≤
      (ARσ.arMeshRotationData σ).arrowChainLength σ a₀.1 a₀.2 + 1 := by
    simpa only [N] using (show 2 ≤ N + 1 by omega)
  have hdBound : d ≤
      (ARσ.arMeshRotationData σ).arrowChainLength σ a₀.1 a₀.2 + 1 := by
    simpa only [N] using (show d ≤ N + 1 by
      dsimp [d]
      omega)
  refine ⟨b, ⟨⟨d, hdLower, hdUpper⟩, ?_⟩⟩
  have htwoRaw := dualArrowChainVertexNat_eq
    σ τ ARσ ARτ D a₀ (e := 2) htwoBound
  have hdRaw := dualArrowChainVertexNat_eq
    σ τ ARσ ARτ D a₀ (e := d) hdBound
  have htwo : ARτ.arrowChainVertexNat τ b₀.1 b₀.2 2 =
      D.forward.labelEquiv
        (ARσ.arrowChainVertexNat σ a₀.1 a₀.2 (N + 1 - 2)) := by
    simpa only [b₀, N] using htwoRaw
  have hd : ARτ.arrowChainVertexNat τ b₀.1 b₀.2 d =
      D.forward.labelEquiv
        (ARσ.arrowChainVertexNat σ a₀.1 a₀.2 (N + 1 - d)) := by
    simpa only [b₀, N] using hdRaw
  change ARτ.arrowChainVertexNat τ b₀.1 b₀.2 2 =
    ARτ.arrowChainVertexNat τ b₀.1 b₀.2 d
  rw [htwo, hd]
  apply congrArg D.forward.labelEquiv
  have hcut := q.2.2
  change ARσ.arrowChainVertexNat σ a₀.1 a₀.2 (N + 1 - 2) =
    ARσ.arrowChainVertexNat σ a₀.1 a₀.2 e at hcut
  rw [show N + 1 - d = e by
    dsimp [d]
    omega]
  exact hcut

/-- The aligned reflected first cut remembers its source chain and last-cut
index. -/
theorem longArrowChainLastDiagonalCutToDualFirst_injective
    [DecidableEq ι] [DecidableEq κ] :
    Function.Injective
      (longArrowChainLastDiagonalCutToDualFirst σ τ ARσ ARτ D) := by
  intro q r h
  rcases q with ⟨qstart, qcut⟩
  rcases r with ⟨rstart, rcut⟩
  let E := dualProjectiveTargetArrowEquiv σ τ ARσ D
  have hdualStart := congrArg Sigma.fst h
  have hdualBase := congrArg
    (fun x : ARτ.LongArrowChainStart τ ↦ x.1) hdualStart
  have hbase : qstart.1 = rstart.1 := by
    apply E.injective
    simpa only [longArrowChainLastDiagonalCutToDualFirst] using hdualBase
  have hstart : qstart = rstart := Subtype.ext hbase
  subst rstart
  apply congrArg (Sigma.mk qstart)
  apply Subtype.ext
  apply Subtype.ext
  have hd := congrArg
    (fun x : ARτ.LongArrowChainFirstDiagonalCut τ ↦ x.2.1.1) h
  let M := ARσ.arMeshRotationData σ
  let N := M.arrowChainLength σ qstart.1.1 qstart.1.2
  let e := qcut.1.1
  let f := rcut.1.1
  have heUpper : e ≤ N + 1 - 2 := by
    simpa only [e, N, M] using qcut.1.2.2
  have hfUpper : f ≤ N + 1 - 2 := by
    simpa only [f, N, M] using rcut.1.2.2
  change N + 1 - e = N + 1 - f at hd
  omega

include D in
/-- The aggregate first diagonal-cut count is invariant under aligned
duality. This is the literal cross-skeleton form of the repaired diagonal
`M4` equality. -/
theorem longArrowChainFirstDiagonalCut_card_eq_aligned
    [DecidableEq ι] [DecidableEq κ] :
    Fintype.card (ARσ.LongArrowChainFirstDiagonalCut σ) =
      Fintype.card (ARτ.LongArrowChainFirstDiagonalCut τ) := by
  let D' := D.swap σ τ
  have hστ :
      Fintype.card (ARσ.LongArrowChainLastDiagonalCut σ) ≤
        Fintype.card (ARτ.LongArrowChainFirstDiagonalCut τ) :=
    Fintype.card_le_of_injective _
      (longArrowChainLastDiagonalCutToDualFirst_injective
        σ τ ARσ ARτ D)
  have hτσ :
      Fintype.card (ARτ.LongArrowChainLastDiagonalCut τ) ≤
        Fintype.card (ARσ.LongArrowChainFirstDiagonalCut σ) :=
    Fintype.card_le_of_injective _
      (longArrowChainLastDiagonalCutToDualFirst_injective
        τ σ ARτ ARσ D')
  have hσ := ARσ.longArrowChainFirstDiagonalCut_card_eq_lastDiagonalCut_card σ
  have hτ := ARτ.longArrowChainFirstDiagonalCut_card_eq_lastDiagonalCut_card τ
  omega

include D in
/-- Source last cuts and aligned-dual first cuts have equal cardinality. -/
theorem longArrowChainLastDiagonalCut_card_eq_dualFirst
    [DecidableEq ι] [DecidableEq κ] :
    Fintype.card (ARσ.LongArrowChainLastDiagonalCut σ) =
      Fintype.card (ARτ.LongArrowChainFirstDiagonalCut τ) := by
  have hσ := ARσ.longArrowChainFirstDiagonalCut_card_eq_lastDiagonalCut_card σ
  have haligned := longArrowChainFirstDiagonalCut_card_eq_aligned
    σ τ ARσ ARτ D
  omega

/-- The reflected-index map is the exact equivalence between source last
cuts and first cuts on the aligned reversed chains. -/
def longArrowChainLastDiagonalCutEquivDualFirst
    [DecidableEq ι] [DecidableEq κ] :
    ARσ.LongArrowChainLastDiagonalCut σ ≃
      ARτ.LongArrowChainFirstDiagonalCut τ :=
  Equiv.ofBijective
    (longArrowChainLastDiagonalCutToDualFirst σ τ ARσ ARτ D)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨longArrowChainLastDiagonalCutToDualFirst_injective
          σ τ ARσ ARτ D,
        longArrowChainLastDiagonalCut_card_eq_dualFirst
          σ τ ARσ ARτ D⟩)

/-- First diagonal cuts themselves are equivalent across aligned duality:
reflect first to last on the source chain, then reverse the chain. -/
def longArrowChainFirstDiagonalCutEquivAligned
    [DecidableEq ι] [DecidableEq κ] :
    ARσ.LongArrowChainFirstDiagonalCut σ ≃
      ARτ.LongArrowChainFirstDiagonalCut τ :=
  (ARσ.longArrowChainFirstDiagonalCutEquivLastDiagonalCut σ).trans
    (longArrowChainLastDiagonalCutEquivDualFirst σ τ ARσ ARτ D)

/-- The aligned equivalence reverses the maximal chain twice—first by the
cut reflection and then by duality—so it retains the displayed cut index. -/
theorem longArrowChainFirstDiagonalCutEquivAligned_index
    [DecidableEq ι] [DecidableEq κ]
    (q : ARσ.LongArrowChainFirstDiagonalCut σ) :
    ((longArrowChainFirstDiagonalCutEquivAligned
      σ τ ARσ ARτ D q).2.1.1) = q.2.1.1 := by
  let e := q.2.1.1
  have he := q.2.1.2
  change
    (ARσ.arMeshRotationData σ).arrowChainLength σ q.1.1.1 q.1.1.2 + 1 -
        ((ARσ.arMeshRotationData σ).arrowChainLength σ
          q.1.1.1 q.1.1.2 + 1 - e) = e
  omega

/-- The aligned first-cut equivalence uses the canonical reversed dual
chain start. -/
theorem longArrowChainFirstDiagonalCutEquivAligned_start
    [DecidableEq ι] [DecidableEq κ]
    (q : ARσ.LongArrowChainFirstDiagonalCut σ) :
    (longArrowChainFirstDiagonalCutEquivAligned
      σ τ ARσ ARτ D q).1.1 =
        dualProjectiveTargetArrowEquiv σ τ ARσ D q.1.1 := by
  rfl

/-- Under aligned reversal, the reverse-last predicate at a first cut of
index `e` becomes the source-side arrow from vertex `N - e` to vertex
`N - 3`.  Thus the total cut equivalence has an exact local correction
law, but does not assert an invalid termwise invariance of the predicate. -/
theorem longArrowChainFirstDiagonalCutEquivAligned_hasReverseLast_iff
    [DecidableEq ι] [DecidableEq κ]
    (q : ARσ.LongArrowChainFirstDiagonalCut σ) :
    let M := ARσ.arMeshRotationData σ
    let N := M.arrowChainLength σ q.1.1.1 q.1.1.2
    let e := q.2.1.1
    ARτ.longArrowChainFirstDiagonalCutHasReverseLast τ
        (longArrowChainFirstDiagonalCutEquivAligned
          σ τ ARσ ARτ D q) ↔
      HasIrreducibleMorphism
        (σ.obj (ARσ.arrowChainVertexNat σ
          q.1.1.1 q.1.1.2 (N - e)))
        (σ.obj (ARσ.arrowChainVertexNat σ
          q.1.1.1 q.1.1.2 (N - 3))) := by
  let M := ARσ.arMeshRotationData σ
  let N := M.arrowChainLength σ q.1.1.1 q.1.1.2
  let e := q.2.1.1
  let q' := longArrowChainFirstDiagonalCutEquivAligned
    σ τ ARσ ARτ D q
  let b := dualProjectiveTargetArrowEquiv σ τ ARσ D q.1.1
  have hN : 4 ≤ N := by
    simpa only [N, M] using q.1.2
  have heLower : 2 ≤ e := q.2.1.2.1
  have heUpper : e ≤ N - 1 := by
    have h := q.2.1.2.2
    change e ≤ N + 1 - 2 at h
    omega
  have hstart : q'.1.1 = b := by
    exact longArrowChainFirstDiagonalCutEquivAligned_start
      σ τ ARσ ARτ D q
  have hindex : q'.2.1.1 = e := by
    exact longArrowChainFirstDiagonalCutEquivAligned_index
      σ τ ARσ ARτ D q
  have hfour := dualArrowChainVertexNat_eq
    σ τ ARσ ARτ D q.1.1 (e := 4) (by
      change 4 ≤ N + 1
      omega)
  have hafter := dualArrowChainVertexNat_eq
    σ τ ARσ ARτ D q.1.1 (e := e + 1) (by
      change e + 1 ≤ N + 1
      omega)
  have hfour' : ARτ.arrowChainVertexNat τ b.1 b.2 4 =
      D.forward.labelEquiv
        (ARσ.arrowChainVertexNat σ q.1.1.1 q.1.1.2 (N - 3)) := by
    simpa only [b, N, M, show N + 1 - 4 = N - 3 by omega] using hfour
  have hafter' : ARτ.arrowChainVertexNat τ b.1 b.2 (e + 1) =
      D.forward.labelEquiv
        (ARσ.arrowChainVertexNat σ q.1.1.1 q.1.1.2 (N - e)) := by
    simpa only [b, N, M, show N + 1 - (e + 1) = N - e by omega]
      using hafter
  have hqfour : ARτ.arrowChainVertexNat τ q'.1.1.1 q'.1.1.2 4 =
      D.forward.labelEquiv
        (ARσ.arrowChainVertexNat σ q.1.1.1 q.1.1.2 (N - 3)) := by
    exact (congrArg
      (fun c : {a : τ.IrreduciblePair // Projective (τ.obj a.1.2)} ↦
        ARτ.arrowChainVertexNat τ c.1 c.2 4) hstart).trans hfour'
  have hqafter :
      ARτ.arrowChainVertexNat τ q'.1.1.1 q'.1.1.2 (q'.2.1.1 + 1) =
        D.forward.labelEquiv
          (ARσ.arrowChainVertexNat σ q.1.1.1 q.1.1.2 (N - e)) := by
    calc
      ARτ.arrowChainVertexNat τ q'.1.1.1 q'.1.1.2 (q'.2.1.1 + 1) =
          ARτ.arrowChainVertexNat τ b.1 b.2 (q'.2.1.1 + 1) :=
        congrArg
          (fun c : {a : τ.IrreduciblePair // Projective (τ.obj a.1.2)} ↦
            ARτ.arrowChainVertexNat τ c.1 c.2 (q'.2.1.1 + 1)) hstart
      _ = ARτ.arrowChainVertexNat τ b.1 b.2 (e + 1) := by
        rw [hindex]
      _ = D.forward.labelEquiv
          (ARσ.arrowChainVertexNat σ q.1.1.1 q.1.1.2 (N - e)) := hafter'
  rw [ARτ.longArrowChainFirstDiagonalCutHasReverseLast_iff τ q',
    hqfour, hqafter]
  exact (D.hasIrreducibleMorphism_image_iff σ τ
    (x := ARσ.arrowChainVertexNat σ
      q.1.1.1 q.1.1.2 (N - e))
    (y := ARσ.arrowChainVertexNat σ
      q.1.1.1 q.1.1.2 (N - 3)))

/-- Source-coordinate form of the reverse-last predicate after aligned
reversal.  For a chain of length `N` and cut index `e`, it is the arrow
from vertex `N - e` to vertex `N - 3`. -/
def longArrowChainFirstDiagonalCutHasAlignedReverseLast
    (q : ARσ.LongArrowChainFirstDiagonalCut σ) : Prop :=
  let M := ARσ.arMeshRotationData σ
  let N := M.arrowChainLength σ q.1.1.1 q.1.1.2
  let e := q.2.1.1
  HasIrreducibleMorphism
    (σ.obj (ARσ.arrowChainVertexNat σ
      q.1.1.1 q.1.1.2 (N - e)))
    (σ.obj (ARσ.arrowChainVertexNat σ
      q.1.1.1 q.1.1.2 (N - 3)))

/-- First cuts whose aligned dual image is a reverse-last exception. -/
abbrev LongArrowChainFirstDiagonalAlignedReverseLastCut :=
  {q : ARσ.LongArrowChainFirstDiagonalCut σ //
    ARσ.longArrowChainFirstDiagonalCutHasAlignedReverseLast σ q}

/-- First cuts whose aligned dual image is regular. -/
abbrev LongArrowChainFirstDiagonalAlignedRegularCut :=
  {q : ARσ.LongArrowChainFirstDiagonalCut σ //
    ¬ ARσ.longArrowChainFirstDiagonalCutHasAlignedReverseLast σ q}

noncomputable instance
    longArrowChainFirstDiagonalAlignedReverseLastCutFintype :
    Fintype (ARσ.LongArrowChainFirstDiagonalAlignedReverseLastCut σ) :=
  Fintype.ofFinite _

noncomputable instance longArrowChainFirstDiagonalAlignedRegularCutFintype :
    Fintype (ARσ.LongArrowChainFirstDiagonalAlignedRegularCut σ) :=
  Fintype.ofFinite _

/-- The corrected aligned reversal identifies its source-coordinate
reverse-last subtype exactly with the ordinary reverse-last subtype on the
dual skeleton. -/
def longArrowChainFirstDiagonalAlignedReverseLastEquivDualReverseLast
    [DecidableEq ι] [DecidableEq κ] :
    ARσ.LongArrowChainFirstDiagonalAlignedReverseLastCut σ ≃
      ARτ.LongArrowChainFirstDiagonalReverseLastCut τ := by
  let E := longArrowChainFirstDiagonalCutEquivAligned
    σ τ ARσ ARτ D
  apply E.subtypeEquiv
  intro q
  exact (longArrowChainFirstDiagonalCutEquivAligned_hasReverseLast_iff
    σ τ ARσ ARτ D q).symm

/-- Likewise, cuts avoiding the source-coordinate transformed exception
are exactly the regular cuts on the aligned dual skeleton. -/
def longArrowChainFirstDiagonalAlignedRegularEquivDualRegular
    [DecidableEq ι] [DecidableEq κ] :
    ARσ.LongArrowChainFirstDiagonalAlignedRegularCut σ ≃
      ARτ.LongArrowChainFirstDiagonalRegularCut τ := by
  let E := longArrowChainFirstDiagonalCutEquivAligned
    σ τ ARσ ARτ D
  apply E.subtypeEquiv
  intro q
  exact not_congr
    (longArrowChainFirstDiagonalCutEquivAligned_hasReverseLast_iff
      σ τ ARσ ARτ D q).symm

/-- Total form of the corrected aligned partition: source first cuts are
exactly dual regular cuts together with dual reverse-last exceptions. -/
def longArrowChainFirstDiagonalCutEquivDualRegularSumReverseLast
    [DecidableEq ι] [DecidableEq κ] :
    ARσ.LongArrowChainFirstDiagonalCut σ ≃
      ARτ.LongArrowChainFirstDiagonalRegularCut τ ⊕
        ARτ.LongArrowChainFirstDiagonalReverseLastCut τ :=
  (longArrowChainFirstDiagonalCutEquivAligned
    σ τ ARσ ARτ D).trans
      (ARτ.longArrowChainFirstDiagonalCutEquivRegularSumReverseLast τ)

section DualM6Occurrence

variable {K : Type u} [Field K] [Algebra K S] [FiniteDimensional K S]

include K ARτ in
/-- Classify every source diagonal cut, after aligned reversal, as either a
genuine dual interior `M6` occurrence or a dual reverse-last correction. -/
def longArrowChainFirstDiagonalCutToDualHookM6OrReverseLast
    [DecidableEq ι] [DecidableEq κ] :
    ARσ.LongArrowChainFirstDiagonalCut σ →
      HookM6Channel.InteriorChannel τ ARτ ⊕
        ARτ.BoundaryM6ReverseLastPair τ :=
  (ARτ.longArrowChainFirstDiagonalCutToHookM6OrReverseLast
      (K := K) τ) ∘
    (longArrowChainFirstDiagonalCutEquivAligned
      σ τ ARσ ARτ D)

include K ARτ in
/-- The aligned dual `M6`/reverse-last classification retains the source
maximal chain and cut index. -/
theorem longArrowChainFirstDiagonalCutToDualHookM6OrReverseLast_injective
    [DecidableEq ι] [DecidableEq κ] :
    Function.Injective
      (longArrowChainFirstDiagonalCutToDualHookM6OrReverseLast
        (K := K) σ τ ARσ ARτ D) :=
  (ARτ.longArrowChainFirstDiagonalCutToHookM6OrReverseLast_injective
      (K := K) τ).comp
    (longArrowChainFirstDiagonalCutEquivAligned
      σ τ ARσ ARτ D).injective

/-- Exact image of the aligned diagonal cuts in the dual signed-channel
occurrence sum. -/
abbrev LongArrowChainFirstDiagonalDualChannelImage
    [DecidableEq ι] [DecidableEq κ] :=
  Set.range
    (longArrowChainFirstDiagonalCutToDualHookM6OrReverseLast
      (K := K) σ τ ARσ ARτ D)

noncomputable instance longArrowChainFirstDiagonalDualChannelImageFintype
    [DecidableEq ι] [DecidableEq κ] :
    Fintype
      (LongArrowChainFirstDiagonalDualChannelImage
        (K := K) σ τ ARσ ARτ D) :=
  Fintype.ofFinite _

include K ARτ in
/-- Source cut coordinates are equivalent to their exact dual
`M6`/reverse-last occurrence image. -/
def longArrowChainFirstDiagonalCutEquivDualChannelImage
    [DecidableEq ι] [DecidableEq κ] :
    ARσ.LongArrowChainFirstDiagonalCut σ ≃
      LongArrowChainFirstDiagonalDualChannelImage
        (K := K) σ τ ARσ ARτ D :=
  Equiv.ofInjective
    (longArrowChainFirstDiagonalCutToDualHookM6OrReverseLast
      (K := K) σ τ ARσ ARτ D)
    (longArrowChainFirstDiagonalCutToDualHookM6OrReverseLast_injective
      (K := K) σ τ ARσ ARτ D)

include K ARτ in
/-- Cardinal form of the exact aligned dual channel image. -/
theorem longArrowChainFirstDiagonalCut_card_eq_dualChannelImage
    [DecidableEq ι] [DecidableEq κ] :
    Fintype.card (ARσ.LongArrowChainFirstDiagonalCut σ) =
      Fintype.card
        (LongArrowChainFirstDiagonalDualChannelImage
          (K := K) σ τ ARσ ARτ D) :=
  Fintype.card_congr
    (longArrowChainFirstDiagonalCutEquivDualChannelImage
      (K := K) σ τ ARσ ARτ D)

include K ARτ in
/-- The aligned source image is not merely equinumerous with the native
target image: it is the same subset of labelled dual
`M6`/reverse-last occurrences. -/
theorem longArrowChainFirstDiagonalDualChannelImage_eq_native
    [DecidableEq ι] [DecidableEq κ] :
    LongArrowChainFirstDiagonalDualChannelImage
        (K := K) σ τ ARσ ARτ D =
      ARτ.LongArrowChainFirstDiagonalChannelImage (K := K) τ := by
  apply Set.ext
  intro p
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨longArrowChainFirstDiagonalCutEquivAligned
      σ τ ARσ ARτ D q, rfl⟩
  · rintro ⟨q, rfl⟩
    refine ⟨(longArrowChainFirstDiagonalCutEquivAligned
      σ τ ARσ ARτ D).symm q, ?_⟩
    simp [longArrowChainFirstDiagonalCutToDualHookM6OrReverseLast]

/-- Complement of the aligned source diagonal image in the actual dual
`M6`/reverse-last occurrence sum. -/
abbrev LongArrowChainFirstDiagonalDualChannelComplement
    [DecidableEq ι] [DecidableEq κ] :=
  {p : HookM6Channel.InteriorChannel τ ARτ ⊕
      ARτ.BoundaryM6ReverseLastPair τ //
    p ∉ LongArrowChainFirstDiagonalDualChannelImage
      (K := K) σ τ ARσ ARτ D}

noncomputable instance
    longArrowChainFirstDiagonalDualChannelComplementFintype
    [DecidableEq ι] [DecidableEq κ] :
    Fintype
      (LongArrowChainFirstDiagonalDualChannelComplement
        (K := K) σ τ ARσ ARτ D) :=
  Fintype.ofFinite _

include K ARτ in
/-- Consequently the aligned-image complement is exactly the native target
diagonal complement, occurrence by occurrence. -/
def longArrowChainFirstDiagonalDualChannelComplementEquivNative
    [DecidableEq ι] [DecidableEq κ] :
    LongArrowChainFirstDiagonalDualChannelComplement
        (K := K) σ τ ARσ ARτ D ≃
      ARτ.LongArrowChainFirstDiagonalChannelComplement (K := K) τ where
  toFun p := ⟨p.1, by
    rw [← longArrowChainFirstDiagonalDualChannelImage_eq_native
      (K := K) σ τ ARσ ARτ D]
    exact p.2⟩
  invFun p := ⟨p.1, by
    rw [longArrowChainFirstDiagonalDualChannelImage_eq_native
      (K := K) σ τ ARσ ARτ D]
    exact p.2⟩
  left_inv p := Subtype.ext rfl
  right_inv p := Subtype.ext rfl

include K ARτ in
/-- Cardinal form of exact complement compatibility. -/
theorem longArrowChainFirstDiagonalDualChannelComplement_card_eq_native
    [DecidableEq ι] [DecidableEq κ] :
    Fintype.card
        (LongArrowChainFirstDiagonalDualChannelComplement
          (K := K) σ τ ARσ ARτ D) =
      Fintype.card
        (ARτ.LongArrowChainFirstDiagonalChannelComplement (K := K) τ) :=
  Fintype.card_congr
    (longArrowChainFirstDiagonalDualChannelComplementEquivNative
      (K := K) σ τ ARσ ARτ D)

end DualM6Occurrence

section DiagonalChannelComplementBalance

variable {K : Type u} [Field K]
  [Algebra K R] [FiniteDimensional K R]
  [Algebra K S] [FiniteDimensional K S]

include K ARσ ARτ D in
/-- Cancelling the aligned diagonal image gives an unconditional crossed
balance between the full native `M6`/reverse-last occurrence sums and their
diagonal complements.  This is the exact subtraction-free form needed when
the same-chain diagonal contribution is combined with the remaining strip
channels. -/
theorem longArrowChainFirstDiagonalChannel_crossedComplement_card_eq
    [DecidableEq ι] [DecidableEq κ] :
    Fintype.card (HookM6Channel.InteriorChannel σ ARσ) +
        Fintype.card (ARσ.BoundaryM6ReverseLastPair σ) +
      Fintype.card
        (ARτ.LongArrowChainFirstDiagonalChannelComplement (K := K) τ) =
    Fintype.card (HookM6Channel.InteriorChannel τ ARτ) +
        Fintype.card (ARτ.BoundaryM6ReverseLastPair τ) +
      Fintype.card
        (ARσ.LongArrowChainFirstDiagonalChannelComplement (K := K) σ) := by
  have hsplitσ := Fintype.card_congr
    (ARσ.longArrowChainFirstDiagonalChannelEquivImageSumComplement
      (K := K) σ)
  have hsplitτ := Fintype.card_congr
    (ARτ.longArrowChainFirstDiagonalChannelEquivImageSumComplement
      (K := K) τ)
  have himageσ := Fintype.card_congr
    (ARσ.longArrowChainFirstDiagonalCutEquivChannelImage
      (K := K) σ)
  have himageτ := Fintype.card_congr
    (ARτ.longArrowChainFirstDiagonalCutEquivChannelImage
      (K := K) τ)
  have haligned := longArrowChainFirstDiagonalCut_card_eq_aligned
    σ τ ARσ ARτ D
  simp only [Fintype.card_sum] at hsplitσ hsplitτ
  omega

include K ARσ ARτ D in
/-- Occurrence-boundary form of the same-chain cancellation: the full
native `M6`/reverse-last sum on either skeleton balances the different-chain
noninjective first-boundary complement on the opposite skeleton. -/
theorem longArrowChainFirstDiagonalChannel_crossedFirstBoundaryComplement_card_eq
    [DecidableEq ι] [DecidableEq κ] :
    Fintype.card (HookM6Channel.InteriorChannel σ ARσ) +
        Fintype.card (ARσ.BoundaryM6ReverseLastPair σ) +
      Fintype.card
        (ARτ.LongArrowChainFirstDiagonalFirstBoundaryComplement τ) =
    Fintype.card (HookM6Channel.InteriorChannel τ ARτ) +
        Fintype.card (ARτ.BoundaryM6ReverseLastPair τ) +
      Fintype.card
        (ARσ.LongArrowChainFirstDiagonalFirstBoundaryComplement σ) := by
  have hcross := longArrowChainFirstDiagonalChannel_crossedComplement_card_eq
    (K := K) σ τ ARσ ARτ D
  have hσ :=
    ARσ.longArrowChainFirstDiagonalChannelComplement_card_eq_firstBoundary
      (K := K) σ
  have hτ :=
    ARτ.longArrowChainFirstDiagonalChannelComplement_card_eq_firstBoundary
      (K := K) τ
  omega

include K ARσ ARτ D in
/-- After splitting off and cancelling the aligned length-three diagonal
remainder, the crossed diagonal-channel balance is stated purely with the
intrinsic different-orbit noninjective first boundary. -/
theorem longArrowChainFirstDiagonalChannel_crossedDifferentOrbitFirstBoundary_card_eq
    [DecidableEq ι] [DecidableEq κ] :
    Fintype.card (HookM6Channel.InteriorChannel σ ARσ) +
        Fintype.card (ARσ.BoundaryM6ReverseLastPair σ) +
      Fintype.card (ARτ.DifferentOrbitFirstSourceNoninjectiveTargetPair τ) =
    Fintype.card (HookM6Channel.InteriorChannel τ ARτ) +
        Fintype.card (ARτ.BoundaryM6ReverseLastPair τ) +
      Fintype.card
        (ARσ.DifferentOrbitFirstSourceNoninjectiveTargetPair σ) := by
  have hcross :=
    longArrowChainFirstDiagonalChannel_crossedFirstBoundaryComplement_card_eq
      (K := K) σ τ ARσ ARτ D
  have hsplitσ :=
    ARσ.longArrowChainFirstDiagonalFirstBoundaryComplement_card_eq_differentOrbit_add_sameOrbit
      σ
  have hsplitτ :=
    ARτ.longArrowChainFirstDiagonalFirstBoundaryComplement_card_eq_differentOrbit_add_sameOrbit
      τ
  have hshort :=
    longArrowChainFirstDiagonalFirstBoundarySameOrbitRemainder_card_eq
      σ τ ARσ ARτ D
  omega

end DiagonalChannelComplementBalance

/-- The exact images of actual labelled diagonal-cut occurrences are
equivalent on the two aligned skeletons. -/
def longArrowChainFirstDiagonalCutOccurrenceImageEquivAligned
    [DecidableEq ι] [DecidableEq κ] :
    ARσ.LongArrowChainFirstDiagonalCutOccurrenceImage σ ≃
      ARτ.LongArrowChainFirstDiagonalCutOccurrenceImage τ :=
  (ARσ.longArrowChainFirstDiagonalCutEquivOccurrenceImage σ).symm |>.trans
    ((longArrowChainFirstDiagonalCutEquivAligned σ τ ARσ ARτ D).trans
      (ARτ.longArrowChainFirstDiagonalCutEquivOccurrenceImage τ))

include D in
/-- Cardinal form of the aligned equality for exact actual labelled
diagonal occurrence images. -/
theorem longArrowChainFirstDiagonalCutOccurrenceImage_card_eq_aligned
    [DecidableEq ι] [DecidableEq κ] :
    Fintype.card (ARσ.LongArrowChainFirstDiagonalCutOccurrenceImage σ) =
      Fintype.card (ARτ.LongArrowChainFirstDiagonalCutOccurrenceImage τ) :=
  Fintype.card_congr
    (longArrowChainFirstDiagonalCutOccurrenceImageEquivAligned
      σ τ ARσ ARτ D)

end FiniteARTranslationData

end OpConjecture.IndecomposableSkeleton
