import OpConjecture.RepresentationTheory.FactorLadder
import OpConjecture.RepresentationTheory.TraceRejective

/-!
# Abstract factor-Hom criterion

This file isolates the representation-theoretic inputs in the
factor-ladder proof.  The closure-to-hole step is proved from the existing
trace model.  Evaluation in the factor category and Iyama's radical-layer
formula are kept as explicit structures rather than asserted as axioms.
-/

noncomputable section

open CategoryTheory

namespace OpConjecture

universe u v w

namespace IndecomposableSkeleton

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)

/-- A label omitted from the selected support `K`. -/
abbrev DeletedLabel (K : Set ι) := {i : ι // i ∉ K}

/-- The trace quotient of a deleted indecomposable is nonzero, expressed
without choosing a quotient object: its trace is a proper submodule. -/
def HasTraceHole (K : Set ι) (x : DeletedLabel K) : Prop :=
  σ.trace K (σ.obj x.1) ≠ ⊤

/-- The dual trace hole: the common kernel of all maps from a deleted
indecomposable to the selected support is nonzero. -/
def HasRejectCohole (K : Set ι) (x : DeletedLabel K) : Prop :=
  σ.reject K (σ.obj x.1) ≠ ⊥

/-- Quotient closure is exactly nonvanishing of the trace hole at every
deleted indecomposable.  This is the first, non-Iyama, part of the paper's
factor-ladder argument. -/
theorem qClosed_iff_all_deleted_have_traceHole (K : Set ι) :
    σ.qClosure.IsClosed K ↔
      ∀ x : DeletedLabel K, HasTraceHole σ K x := by
  constructor
  · intro hclosed x htop
    have hclosure : σ.qClosure K = K :=
      σ.qClosure.isClosed_iff.mp hclosed
    have hxcl : x.1 ∈ σ.qClosure K :=
      (mem_qClosure_iff_trace_eq_top σ K x.1).2 htop
    rw [hclosure] at hxcl
    exact x.2 hxcl
  · intro hholes
    apply σ.qClosure.isClosed_iff.2
    apply Set.Subset.antisymm
    · intro i hi
      by_contra hiK
      exact hholes ⟨i, hiK⟩
        ((mem_qClosure_iff_trace_eq_top σ K i).1 hi)
    · exact σ.qClosure.le_closure K

/-- The direct dual closure-to-hole statement. -/
theorem sClosed_iff_all_deleted_have_rejectCohole (K : Set ι) :
    σ.sClosure.IsClosed K ↔
      ∀ x : DeletedLabel K, HasRejectCohole σ K x := by
  constructor
  · intro hclosed x hbot
    have hclosure : σ.sClosure K = K :=
      σ.sClosure.isClosed_iff.mp hclosed
    have hxcl : x.1 ∈ σ.sClosure K :=
      (mem_sClosure_iff_reject_eq_bot σ K x.1).2 hbot
    rw [hclosure] at hxcl
    exact x.2 hxcl
  · intro hholes
    apply σ.sClosure.isClosed_iff.2
    apply Set.Subset.antisymm
    · intro i hi
      by_contra hiK
      exact hholes ⟨i, hiK⟩
        ((mem_sClosure_iff_reject_eq_bot σ K i).1 hi)
    · exact σ.sClosure.le_closure K

/-- The factor-category input preceding Iyama's radical-layer formula.

`factorHomNonzero p x` represents
`((mod R)/[add K])(obj p, obj x) ≠ 0`.  The equivalence field packages:

* evaluation at `1`, identifying the trace hole with factor Hom out of the
  regular module;
* decomposition of the regular module into indecomposable projectives;
* vanishing of sources belonging to `K` in the factor category.

Thus `P` must be instantiated by the deleted indecomposable projectives. -/
structure HoleFactorHomInput
    (K : Set ι) (P : Set (DeletedLabel K)) where
  factorHomNonzero :
    DeletedLabel K → DeletedLabel K → Prop
  hole_iff_projective_factorHom :
    ∀ x : DeletedLabel K,
      HasTraceHole σ K x ↔
        ∃ p : DeletedLabel K,
          p ∈ P ∧ factorHomNonzero p x

/-- Dual factor-category input for reverse ladders.  The predicate is
oriented as `(injective boundary, starting label)` so that it can be fed to
the same abstract ladder-layer interface. -/
structure RejectFactorHomInput
    (K : Set ι) (I : Set (DeletedLabel K)) where
  reverseFactorHomNonzero :
    DeletedLabel K → DeletedLabel K → Prop
  cohole_iff_injective_factorHom :
    ∀ x : DeletedLabel K,
      HasRejectCohole σ K x ↔
        ∃ i : DeletedLabel K,
          i ∈ I ∧ reverseFactorHomNonzero i x

end IndecomposableSkeleton

namespace FactorLadder

/-- Explicit interface for the imported Iyama radical-layer result.

`layerNonzero n p x` represents nonvanishing at `p` of the `n`-th radical
layer of the factor-category representable at `x`.  The first equivalence
is the nilpotent-radical filtration step.  The second is the projective-cover
and radical-layer formula.  Eventual vanishing records the other conclusion
of the factor-ladder proposition, although the criterion itself does not
need it after the first equivalence has been supplied. -/
structure IyamaRadicalLayerInput {D : Type v}
    (A : Data D) (factorHomNonzero : D → D → Prop) where
  layerNonzero : ℕ → D → D → Prop
  factorHom_iff_exists_layer :
    ∀ p x : D,
      factorHomNonzero p x ↔
        ∃ n, layerNonzero n p x
  layer_nonzero_iff_ladder_occurs :
    ∀ n (p x : D),
      layerNonzero n p x ↔
        0 < A.ladder x n p
  eventually_ladder_zero :
    ∀ x : D, ∃ N, ∀ n, N ≤ n → A.ladder x n = 0

namespace IyamaRadicalLayerInput

/-- The exact factor-Hom/nonzero-coefficient consequence consumed by the
closure criterion. -/
theorem factorHom_iff_ladder_occurs
    {D : Type v} {A : Data D}
    {factorHomNonzero : D → D → Prop}
    (I : IyamaRadicalLayerInput A factorHomNonzero)
    (p x : D) :
    factorHomNonzero p x ↔
      ∃ n, 0 < A.ladder x n p := by
  rw [I.factorHom_iff_exists_layer]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, (I.layer_nonzero_iff_ladder_occurs n p x).1 hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, (I.layer_nonzero_iff_ladder_occurs n p x).2 hn⟩

end IyamaRadicalLayerInput

end FactorLadder

namespace IndecomposableSkeleton

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)

/-- Abstract factor-ladder criterion with the two genuinely
representation-theoretic bridges exposed as hypotheses. -/
theorem qClosed_iff_every_deleted_ladder_reaches_projective
    (K : Set ι)
    (A : FactorLadder.Data (DeletedLabel K))
    (P : Set (DeletedLabel K))
    (H : HoleFactorHomInput σ K P)
    (I : FactorLadder.IyamaRadicalLayerInput A H.factorHomNonzero) :
    σ.qClosure.IsClosed K ↔
      ∀ x : DeletedLabel K,
        A.ReachesBoundary P x := by
  rw [qClosed_iff_all_deleted_have_traceHole σ K]
  constructor
  · intro hholes x
    obtain ⟨p, hp, hhom⟩ :=
      (H.hole_iff_projective_factorHom x).1 (hholes x)
    obtain ⟨n, hn⟩ :=
      (I.factorHom_iff_ladder_occurs p x).1 hhom
    exact ⟨n, p, hp, hn⟩
  · intro hreach x
    obtain ⟨n, p, hp, hn⟩ := hreach x
    apply (H.hole_iff_projective_factorHom x).2
    exact
      ⟨p, hp, (I.factorHom_iff_ladder_occurs p x).2 ⟨n, hn⟩⟩

/-- Literal `add K` form of the same criterion. -/
theorem generated_isClosedUnderQuotients_iff_every_deleted_ladder_reaches_projective
    (K : Set ι)
    (A : FactorLadder.Data (DeletedLabel K))
    (P : Set (DeletedLabel K))
    (H : HoleFactorHomInput σ K P)
    (I : FactorLadder.IyamaRadicalLayerInput A H.factorHomNonzero) :
    (σ.generated K).carrier.IsClosedUnderQuotients ↔
      ∀ x : DeletedLabel K,
        A.ReachesBoundary P x :=
  (qClosed_iff_generated_isClosedUnderQuotients σ K).symm.trans
    (qClosed_iff_every_deleted_ladder_reaches_projective
      σ K A P H I)

/-- Dual factor-ladder criterion with the reverse factor-category and
radical-layer bridges exposed explicitly. -/
theorem sClosed_iff_every_deleted_reverseLadder_reaches_injective
    (K : Set ι)
    (A : FactorLadder.Data (DeletedLabel K))
    (P : Set (DeletedLabel K))
    (H : RejectFactorHomInput σ K P)
    (I : FactorLadder.IyamaRadicalLayerInput
      A H.reverseFactorHomNonzero) :
    σ.sClosure.IsClosed K ↔
      ∀ x : DeletedLabel K,
        A.ReachesBoundary P x := by
  rw [sClosed_iff_all_deleted_have_rejectCohole σ K]
  constructor
  · intro hholes x
    obtain ⟨p, hp, hhom⟩ :=
      (H.cohole_iff_injective_factorHom x).1 (hholes x)
    obtain ⟨n, hn⟩ :=
      (I.factorHom_iff_ladder_occurs p x).1 hhom
    exact ⟨n, p, hp, hn⟩
  · intro hreach x
    obtain ⟨n, p, hp, hn⟩ := hreach x
    apply (H.cohole_iff_injective_factorHom x).2
    exact
      ⟨p, hp, (I.factorHom_iff_ladder_occurs p x).2 ⟨n, hn⟩⟩

/-- Literal `add K` form of the reverse-ladder criterion. -/
theorem generated_isClosedUnderSubobjects_iff_every_deleted_reverseLadder_reaches_injective
    (K : Set ι)
    (A : FactorLadder.Data (DeletedLabel K))
    (P : Set (DeletedLabel K))
    (H : RejectFactorHomInput σ K P)
    (I : FactorLadder.IyamaRadicalLayerInput
      A H.reverseFactorHomNonzero) :
    (σ.generated K).carrier.IsClosedUnderSubobjects ↔
      ∀ x : DeletedLabel K,
        A.ReachesBoundary P x :=
  (sClosed_iff_generated_isClosedUnderSubobjects σ K).symm.trans
    (sClosed_iff_every_deleted_reverseLadder_reaches_injective
      σ K A P H I)

end IndecomposableSkeleton

end OpConjecture
