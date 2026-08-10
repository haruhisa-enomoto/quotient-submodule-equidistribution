import OpConjecture.RepresentationDirected.DualDirectedOrder
import OpConjecture.RepresentationDirected.OrderedARWord
import OpConjecture.RepresentationDirected.SimpleGraphBruhatReversal
import OpConjecture.RepresentationTheory.AlmostSplitDuality

/-!
# Auslander--Reiten words under duality

This file proves the categorical compatibility needed to identify an opposite
AR word with the reverse of the source word.  Minimal almost-split maps and
their kernels/cokernels are transported through an aligned biduality, giving
exact reversal of AR translation steps and hence of orbit-labelled letters.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace OpConjecture.RepresentationDirected.ARWordDuality

open DirectedAROrbit
open DualDirectedOrder
open FixedWordSubwords

universe uR uS uI uK

variable
    {R : Type uR} [Ring R] [IsNoetherianRing R]
    {S : Type uS} [Ring S] [IsNoetherianRing S]
    {I : Type uI} {Kappa : Type uK}
    (sigma : IndecomposableSkeleton.{uR, uI, uR} R I)
    (tau : IndecomposableSkeleton.{uS, uK, uS} S Kappa)

/-- The compatibility predicate saying that an aligned biduality reverses the
selected one-step AR relations. -/
def ARStepReversedBy
    (B : tau.AlignedBiduality sigma)
    (Dsigma : sigma.FiniteARTranslationData)
    (Dtau : tau.FiniteARTranslationData) : Prop :=
  ∀ x y : Kappa,
    ARStep tau Dtau x y ↔
      ARStep sigma Dsigma
        (B.forward.labelEquiv y) (B.forward.labelEquiv x)

/-- The left map obtained by applying an aligned anti-equivalence to a chosen
right AR map. -/
def transportedRightARMap
    (D : tau.AlignedAntiEquivalence sigma)
    (Ttau : tau.FiniteARTranslationData)
    (y : tau.NonprojectiveLabel) :
    sigma.obj (D.labelEquiv y.1) ⟶
      D.categoryEquiv.functor.obj
        (Opposite.op (Ttau.chosenRightAR tau y).middle) :=
  (D.objIso y.1).inv ≫
    D.categoryEquiv.functor.map (Ttau.chosenRightAR tau y).map.op

/-- The cokernel of the transported right AR map is the representative dual
to the original AR kernel. -/
def transportedRightARCokernelIso
    (D : tau.AlignedAntiEquivalence sigma)
    (Ttau : tau.FiniteARTranslationData)
    (y : tau.NonprojectiveLabel) :
    cokernel (transportedRightARMap sigma tau D Ttau y) ≅
      sigma.obj (D.labelEquiv (Ttau.arTranslation tau y).1) :=
  (OpConjecture.cokernelPrecompMapOpIsoKernel D.categoryEquiv
      (Ttau.chosenRightAR tau y).map (D.objIso y.1).symm).trans <|
    (D.categoryEquiv.functor.mapIso
      (Ttau.arTranslationKernelIso tau y).op.symm).trans <|
        D.objIso (Ttau.arTranslation tau y).1

/-- Step reversal transports every finite translation path, reversing its
direction. -/
theorem arReach_reversed_of_arReach
    (B : tau.AlignedBiduality sigma)
    (Dsigma : sigma.FiniteARTranslationData)
    (Dtau : tau.FiniteARTranslationData)
    (hstep : ARStepReversedBy sigma tau B Dsigma Dtau)
    {x y : Kappa}
    (hxy : Relation.ReflTransGen (ARStep tau Dtau) x y) :
    Relation.ReflTransGen (ARStep sigma Dsigma)
      (B.forward.labelEquiv y) (B.forward.labelEquiv x) := by
  have hswap :
      Relation.ReflTransGen
        (Function.swap (ARStep sigma Dsigma))
        (B.forward.labelEquiv x) (B.forward.labelEquiv y) :=
    Relation.ReflTransGen.lift
      (r := ARStep tau Dtau)
      (p := Function.swap (ARStep sigma Dsigma))
      B.forward.labelEquiv
      (fun a b h ↦ (hstep a b).1 h) x y hxy
  exact (Relation.reflTransGen_swap (r := ARStep sigma Dsigma)).1 hswap

variable [Fintype I] [Fintype Kappa]

omit [Fintype Kappa] in
/-- An aligned anti-equivalence reverses the single AR step ending at a
specified nonprojective label. -/
theorem arStep_reversed_at
    (D : tau.AlignedAntiEquivalence sigma)
    (Tsigma : sigma.FiniteARTranslationData)
    (Ttau : tau.FiniteARTranslationData)
    (y : tau.NonprojectiveLabel) :
    ARStep sigma Tsigma
      (D.labelEquiv y.1) (D.labelEquiv (Ttau.arTranslation tau y).1) := by
  let sy : sigma.NoninjectiveLabel :=
    ⟨D.labelEquiv y.1, by
      intro hi
      exact y.2
        ((injective_labelEquiv_iff_projective tau sigma D y.1).1 hi)⟩
  let z : sigma.NonprojectiveLabel :=
    (Tsigma.arTranslationEquiv sigma).symm sy
  let A := Ttau.chosenRightAR tau y
  let g := transportedRightARMap sigma tau D Ttau y
  have hgAS : IsLeftAlmostSplit g :=
    (A.rightAlmostSplit.map_op_equivalence D.categoryEquiv).precomp_iso
      (D.objIso y.1).symm
  have hgMin : IsLeftMinimal g :=
    (A.rightMinimal.map_op_equivalence D.categoryEquiv).precomp_iso
      (D.objIso y.1).symm
  let L := Tsigma.chosenLeftAR sigma sy
  obtain ⟨ec⟩ := OpConjecture.nonempty_cokernelIso_of_leftAlmostSplit
    hgAS hgMin L.leftAlmostSplit L.leftMinimal
  let eg : cokernel g ≅
      sigma.obj (D.labelEquiv (Ttau.arTranslation tau y).1) :=
    transportedRightARCokernelIso sigma tau D Ttau y
  let el : cokernel L.map ≅ sigma.obj z.1 :=
    Tsigma.chosenLeftARCokernelIso sigma sy
  have hlabel : D.labelEquiv (Ttau.arTranslation tau y).1 = z.1 := by
    apply sigma.eq_of_iso
    exact ⟨eg.symm.trans (ec.trans el)⟩
  refine ⟨z, ?_, hlabel⟩
  exact congrArg Subtype.val
    ((Tsigma.arTranslationEquiv sigma).apply_symm_apply sy) |>.symm

/-- The two halves of an aligned biduality prove exact reversal of the full
AR-step relation. -/
theorem arStepReversedBy_of_alignedBiduality
    (B : tau.AlignedBiduality sigma)
    (Tsigma : sigma.FiniteARTranslationData)
    (Ttau : tau.FiniteARTranslationData) :
    ARStepReversedBy sigma tau B Tsigma Ttau := by
  intro x y
  constructor
  · rintro ⟨z, rfl, rfl⟩
    exact arStep_reversed_at sigma tau B.forward Tsigma Ttau z
  · rintro ⟨z, hfirst, hsecond⟩
    have hrev :=
      arStep_reversed_at tau sigma B.backward Ttau Tsigma z
    have hz : B.backward.labelEquiv z.1 = x := by
      rw [B.backward_label, ← hsecond]
      exact B.forward.labelEquiv.symm_apply_apply x
    have htau :
        B.backward.labelEquiv (Tsigma.arTranslation sigma z).1 = y := by
      rw [B.backward_label, ← hfirst]
      exact B.forward.labelEquiv.symm_apply_apply y
    simpa only [hz, htau] using hrev

/-- Relabel an opposite projective orbit by dualizing its projective end to
the source injective end and then taking the projective end of that source
orbit. -/
def dualOrbitLabelEquiv
    (B : tau.AlignedBiduality sigma)
    (Hsigma : HasAcyclicNonzeroNonisomorphisms sigma)
    (Dsigma : sigma.FiniteARTranslationData) :
    ProjectiveLabel tau ≃ ProjectiveLabel sigma :=
  (projectiveLabelEquivDualInjectiveLabel tau sigma B.forward).trans
    (projectiveLabelEquivInjectiveLabel sigma Hsigma Dsigma).symm

/-- Once one-step AR reversal is supplied, the relabeled opposite orbit
label of every object is exactly the source orbit label of its dual object. -/
theorem dualOrbitLabelEquiv_arOrbitLabel
    (B : tau.AlignedBiduality sigma)
    (Hsigma : HasAcyclicNonzeroNonisomorphisms sigma)
    (Htau : HasAcyclicNonzeroNonisomorphisms tau)
    (Dsigma : sigma.FiniteARTranslationData)
    (Dtau : tau.FiniteARTranslationData)
    (hstep : ARStepReversedBy sigma tau B Dsigma Dtau)
    (x : Kappa) :
    dualOrbitLabelEquiv sigma tau B Hsigma Dsigma
        (arOrbitLabel tau Htau Dtau x) =
      arOrbitLabel sigma Hsigma Dsigma (B.forward.labelEquiv x) := by
  let p : ProjectiveLabel tau := arOrbitLabel tau Htau Dtau x
  have hpx : Relation.ReflTransGen (ARStep tau Dtau) p.1 x :=
    arOrbitLabel_reaches tau Htau Dtau x
  have hdualReach : Relation.ReflTransGen (ARStep sigma Dsigma)
      (B.forward.labelEquiv x) (B.forward.labelEquiv p.1) :=
    arReach_reversed_of_arReach sigma tau B Dsigma Dtau hstep hpx
  have hdualInjective : Injective
      (sigma.obj (B.forward.labelEquiv p.1)) :=
    (injective_labelEquiv_iff_projective
      tau sigma B.forward p.1).2 p.2
  have htop :
      arOrbitInjectiveLabel sigma Hsigma Dsigma
          (B.forward.labelEquiv x) =
        ⟨B.forward.labelEquiv p.1, hdualInjective⟩ :=
    arOrbitInjectiveLabel_eq_of_injective_descendant
      sigma Hsigma Dsigma hdualInjective hdualReach
  change
    (projectiveLabelEquivInjectiveLabel sigma Hsigma Dsigma).symm
        ⟨B.forward.labelEquiv p.1, hdualInjective⟩ =
      arOrbitLabel sigma Hsigma Dsigma (B.forward.labelEquiv x)
  rw [← htop]
  change
    arOrbitLabel sigma Hsigma Dsigma
        (arOrbitInjectiveLabel sigma Hsigma Dsigma
          (B.forward.labelEquiv x)).1 =
      arOrbitLabel sigma Hsigma Dsigma (B.forward.labelEquiv x)
  exact (arOrbitLabel_eq_of_reaches sigma Hsigma Dsigma
    (reaches_arOrbitInjectiveLabel sigma Hsigma Dsigma
      (B.forward.labelEquiv x))).symm

/-- Unconditional orbit-label alignment supplied by the categorical
AR-step reversal theorem. -/
theorem dualOrbitLabelEquiv_arOrbitLabel_of_alignedBiduality
    (B : tau.AlignedBiduality sigma)
    (Hsigma : HasAcyclicNonzeroNonisomorphisms sigma)
    (Htau : HasAcyclicNonzeroNonisomorphisms tau)
    (Dsigma : sigma.FiniteARTranslationData)
    (Dtau : tau.FiniteARTranslationData)
    (x : Kappa) :
    dualOrbitLabelEquiv sigma tau B Hsigma Dsigma
        (arOrbitLabel tau Htau Dtau x) =
      arOrbitLabel sigma Hsigma Dsigma (B.forward.labelEquiv x) :=
  dualOrbitLabelEquiv_arOrbitLabel sigma tau B Hsigma Htau Dsigma Dtau
    (arStepReversedBy_of_alignedBiduality sigma tau B Dsigma Dtau) x

/-- The explicit target order obtained by reversing a specified source order
through the backward half of a biduality. -/
def oppositeOrderChoice
    (B : tau.AlignedBiduality sigma)
    (E : DirectedOrderChoice sigma) : DirectedOrderChoice tau := by
  letI := E.order
  refine
    { order := reversePullbackLinearOrder B.forward.labelEquiv
      homOrderProperty := ?_ }
  intro a b f hf hab
  have h :=
    (dual_homOrderProperty sigma tau B.backward E.homOrderProperty) f hf hab
  simpa [dualLinearOrder, B.backward_label] using h

/-- Reverse positions between the explicit opposite and source AR words. -/
def reverseWordPositionEquiv
    (B : tau.AlignedBiduality sigma)
    (Hsigma : HasAcyclicNonzeroNonisomorphisms sigma)
    (Htau : HasAcyclicNonzeroNonisomorphisms tau)
    (Dsigma : sigma.FiniteARTranslationData)
    (Dtau : tau.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma) :
    Fin (DirectedAROrbit.OrderedARWord.wordFor tau Htau Dtau
        (oppositeOrderChoice sigma tau B E)).length ≃
      Fin (DirectedAROrbit.OrderedARWord.wordFor sigma Hsigma Dsigma E).length :=
  (finCongr (DirectedAROrbit.OrderedARWord.wordFor_length tau Htau Dtau
      (oppositeOrderChoice sigma tau B E))).trans <|
    (finCongr (Fintype.card_congr B.forward.labelEquiv)).trans <|
      Fin.revPerm.trans <|
        (finCongr (DirectedAROrbit.OrderedARWord.wordFor_length
          sigma Hsigma Dsigma E)).symm

/-- The canonical positions of the explicitly reversed target order are
exactly the reversed canonical positions of the source order. -/
@[simp]
theorem positionEquivFor_oppositeOrderChoice_dual
    (B : tau.AlignedBiduality sigma)
    (Hsigma : HasAcyclicNonzeroNonisomorphisms sigma)
    (Htau : HasAcyclicNonzeroNonisomorphisms tau)
    (Dsigma : sigma.FiniteARTranslationData)
    (Dtau : tau.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (p : Fin (DirectedAROrbit.OrderedARWord.wordFor tau Htau Dtau
      (oppositeOrderChoice sigma tau B E)).length) :
    B.forward.labelEquiv
        (DirectedAROrbit.OrderedARWord.positionEquivFor tau Htau Dtau
          (oppositeOrderChoice sigma tau B E) p) =
      DirectedAROrbit.OrderedARWord.positionEquivFor sigma Hsigma Dsigma E
        (reverseWordPositionEquiv sigma tau B Hsigma Htau Dsigma Dtau E p) := by
  letI := E.order
  letI : LinearOrder Kappa :=
    reversePullbackLinearOrder B.forward.labelEquiv
  have h := canonicalPosition_reversePullback
    (I := I) (Kappa := Kappa) B.forward.labelEquiv
    (finCongr (DirectedAROrbit.OrderedARWord.wordFor_length tau Htau Dtau
      (oppositeOrderChoice sigma tau B E)) p)
  unfold DirectedAROrbit.OrderedARWord.positionEquivFor
  unfold DirectedAROrbit.OrderedARWord.orderedObjectEquivFor
  simp only [oppositeOrderChoice]
  change B.forward.labelEquiv
      ((Fintype.orderIsoFinOfCardEq Kappa rfl)
        (finCongr (DirectedAROrbit.OrderedARWord.wordFor_length
          tau Htau Dtau (oppositeOrderChoice sigma tau B E)) p)) =
    (Fintype.orderIsoFinOfCardEq I rfl)
      (finCongr (DirectedAROrbit.OrderedARWord.wordFor_length
        sigma Hsigma Dsigma E)
        (reverseWordPositionEquiv
          sigma tau B Hsigma Htau Dsigma Dtau E p))
  rw [show finCongr (DirectedAROrbit.OrderedARWord.wordFor_length
      sigma Hsigma Dsigma E)
      (reverseWordPositionEquiv
        sigma tau B Hsigma Htau Dsigma Dtau E p) =
    Fin.rev (finCongr (Fintype.card_congr B.forward.labelEquiv)
      (finCongr (DirectedAROrbit.OrderedARWord.wordFor_length
        tau Htau Dtau (oppositeOrderChoice sigma tau B E)) p)) by rfl]
  exact h

/-- Pointwise form of the paper's reverse-word statement: after the canonical
orbit relabeling, the target letter at every explicit opposite position is
the source letter at the reversed position. -/
theorem label_wordFor_oppositeOrderChoice
    (B : tau.AlignedBiduality sigma)
    (Hsigma : HasAcyclicNonzeroNonisomorphisms sigma)
    (Htau : HasAcyclicNonzeroNonisomorphisms tau)
    (Dsigma : sigma.FiniteARTranslationData)
    (Dtau : tau.FiniteARTranslationData)
    (hstep : ARStepReversedBy sigma tau B Dsigma Dtau)
    (E : DirectedOrderChoice sigma)
    (p : Fin (DirectedAROrbit.OrderedARWord.wordFor tau Htau Dtau
      (oppositeOrderChoice sigma tau B E)).length) :
    dualOrbitLabelEquiv sigma tau B Hsigma Dsigma
        (ARWord.label
          (DirectedAROrbit.OrderedARWord.wordFor tau Htau Dtau
            (oppositeOrderChoice sigma tau B E)) p) =
      ARWord.label
        (DirectedAROrbit.OrderedARWord.wordFor sigma Hsigma Dsigma E)
        (reverseWordPositionEquiv
          sigma tau B Hsigma Htau Dsigma Dtau E p) := by
  rw [DirectedAROrbit.OrderedARWord.label_wordFor,
    dualOrbitLabelEquiv_arOrbitLabel sigma tau B Hsigma Htau
      Dsigma Dtau hstep,
    DirectedAROrbit.OrderedARWord.label_wordFor,
    positionEquivFor_oppositeOrderChoice_dual]

/-- Unconditional pointwise reverse-word theorem under an aligned
biduality. -/
theorem label_wordFor_oppositeOrderChoice_of_alignedBiduality
    (B : tau.AlignedBiduality sigma)
    (Hsigma : HasAcyclicNonzeroNonisomorphisms sigma)
    (Htau : HasAcyclicNonzeroNonisomorphisms tau)
    (Dsigma : sigma.FiniteARTranslationData)
    (Dtau : tau.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (p : Fin (DirectedAROrbit.OrderedARWord.wordFor tau Htau Dtau
      (oppositeOrderChoice sigma tau B E)).length) :
    dualOrbitLabelEquiv sigma tau B Hsigma Dsigma
        (ARWord.label
          (DirectedAROrbit.OrderedARWord.wordFor tau Htau Dtau
            (oppositeOrderChoice sigma tau B E)) p) =
      ARWord.label
        (DirectedAROrbit.OrderedARWord.wordFor sigma Hsigma Dsigma E)
        (reverseWordPositionEquiv
          sigma tau B Hsigma Htau Dsigma Dtau E p) :=
  label_wordFor_oppositeOrderChoice sigma tau B Hsigma Htau Dsigma Dtau
    (arStepReversedBy_of_alignedBiduality sigma tau B Dsigma Dtau) E p

/-- List-valued form of the paper's reverse-word statement: relabeling the
explicit opposite AR word by duality gives the literal reverse of the source
AR word. -/
theorem map_wordFor_oppositeOrderChoice_eq_reverse
    (B : tau.AlignedBiduality sigma)
    (Hsigma : HasAcyclicNonzeroNonisomorphisms sigma)
    (Htau : HasAcyclicNonzeroNonisomorphisms tau)
    (Dsigma : sigma.FiniteARTranslationData)
    (Dtau : tau.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma) :
    (DirectedAROrbit.OrderedARWord.wordFor tau Htau Dtau
        (oppositeOrderChoice sigma tau B E)).map
        (dualOrbitLabelEquiv sigma tau B Hsigma Dsigma) =
      (DirectedAROrbit.OrderedARWord.wordFor
        sigma Hsigma Dsigma E).reverse := by
  let WT := DirectedAROrbit.OrderedARWord.wordFor tau Htau Dtau
    (oppositeOrderChoice sigma tau B E)
  let WS := DirectedAROrbit.OrderedARWord.wordFor sigma Hsigma Dsigma E
  apply List.ext_get
  · simpa only [List.length_map, List.length_reverse, WT, WS,
      DirectedAROrbit.OrderedARWord.wordFor_length] using
      Fintype.card_congr B.forward.labelEquiv
  · intro n hnT hnS
    let p : Fin WT.length := ⟨n, by simpa [WT] using hnT⟩
    let q : Fin WS.length :=
      reverseWordPositionEquiv sigma tau B Hsigma Htau Dsigma Dtau E p
    have hletter :
        dualOrbitLabelEquiv sigma tau B Hsigma Dsigma (WT.get p) =
          WS.get q := by
      simpa only [ARWord.label, WT, WS, q] using
        label_wordFor_oppositeOrderChoice_of_alignedBiduality
          sigma tau B Hsigma Htau Dsigma Dtau E p
    have hnI : n < Fintype.card I := by
      simpa [WS] using hnS
    have hposition : reverseIndexEquiv WS q = ⟨n, hnS⟩ := by
      apply Fin.ext
      simp [q, p, reverseWordPositionEquiv, reverseIndexEquiv, WT, WS,
        Fin.rev]
      omega
    calc
      (WT.map (dualOrbitLabelEquiv sigma tau B Hsigma Dsigma)).get
          ⟨n, hnT⟩ =
          dualOrbitLabelEquiv sigma tau B Hsigma Dsigma (WT.get p) := by
            simp [p]
      _ = WS.get q := hletter
      _ = WS.reverse.get (reverseIndexEquiv WS q) :=
        (get_reverse_reverseIndexEquiv WS q).symm
      _ = WS.reverse.get ⟨n, hnS⟩ := by rw [hposition]

universe uL

open FixedWordSubwords

omit [Fintype I] [Fintype Kappa] in
/-- Given source positions, reverse them and pull them back through the
duality label equivalence.  This is the exact position equivalence consumed
by `ReversedQuotientProfileData`. -/
def synchronizedOppositePosition
    {L : Type uL} {Q : List L}
    (B : tau.AlignedBiduality sigma)
    (sourcePosition : Fin Q.length ≃ I) :
    Fin Q.reverse.length ≃ Kappa :=
  (reverseIndexEquiv Q).symm |>.trans <|
    sourcePosition.trans B.forward.labelEquiv.symm

omit [Fintype I] [Fintype Kappa] in
@[simp]
theorem synchronizedOppositePosition_dual
    {L : Type uL} {Q : List L}
    (B : tau.AlignedBiduality sigma)
    (sourcePosition : Fin Q.length ≃ I)
    (p : Fin Q.reverse.length) :
    B.forward.labelEquiv
        (synchronizedOppositePosition sigma tau B sourcePosition p) =
      sourcePosition ((reverseIndexEquiv Q).symm p) := by
  simp [synchronizedOppositePosition]

end OpConjecture.RepresentationDirected.ARWordDuality
