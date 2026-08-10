import QuotientSubmoduleEquidistribution.RepresentationDirected.DirectedAROrbits
import QuotientSubmoduleEquidistribution.RepresentationTheory.DualFixedSocleTransport

/-!
# Directed orders under an anti-equivalence

This file constructs the synchronized order needed for the manuscript's
opposite-algebra argument.  Given an explicit Hom order on a finite
indecomposable skeleton, an aligned anti-equivalence gives the reverse Hom
order on the dual skeleton.  It also exchanges the projective and injective
ends of Auslander--Reiten translation orbits.

There is no concrete algebra or module classification in this file.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.RepresentationDirected.DualDirectedOrder

universe uR uS uI uK

variable
    {R : Type uR} [Ring R] [IsNoetherianRing R]
    {S : Type uS} [Ring S] [IsNoetherianRing S]
    {I : Type uI} {Kappa : Type uK}
    (sigma : IndecomposableSkeleton.{uR, uI, uR} R I)
    (tau : IndecomposableSkeleton.{uS, uK, uS} S Kappa)
    (D : sigma.AlignedAntiEquivalence tau)

/-- Pull the reverse of a linear order back along an equivalence. -/
abbrev reversePullbackLinearOrder
    [LinearOrder I] (e : Kappa ≃ I) : LinearOrder Kappa :=
  LinearOrder.lift'
    (fun x : Kappa ↦ (show OrderDual I from e x)) e.injective

@[simp]
theorem reversePullbackLinearOrder_lt_iff
    [LinearOrder I] (e : Kappa ≃ I) (x y : Kappa) :
    letI := reversePullbackLinearOrder e
    x < y ↔ e y < e x := by
  rfl

/-- The target order obtained by reversing the source order through an
aligned anti-equivalence. -/
abbrev dualLinearOrder [LinearOrder I] : LinearOrder Kappa :=
  reversePullbackLinearOrder D.labelEquiv.symm

@[simp]
theorem dualLinearOrder_lt_iff [LinearOrder I] (a b : Kappa) :
    letI := dualLinearOrder sigma tau D
    a < b ↔ D.labelEquiv.symm b < D.labelEquiv.symm a := by
  rfl

/-- A nonzero target morphism remains nonzero after taking its chosen source
preimage under the aligned anti-equivalence. -/
theorem undualMap_ne_zero
    {i j : I}
    (g : tau.obj (D.labelEquiv j) ⟶ tau.obj (D.labelEquiv i))
    (hg : g ≠ 0) :
    QuotientSubmoduleEquidistribution.DualFixedSocleTransport.undualMap sigma tau D g ≠ 0 := by
  intro hz
  apply hg
  let h := (D.objIso j).hom ≫ g ≫ (D.objIso i).inv
  have hpre : D.categoryEquiv.functor.preimage h = 0 := by
    apply Quiver.Hom.unop_inj
    simpa [h, QuotientSubmoduleEquidistribution.DualFixedSocleTransport.undualMap] using hz
  have hmap := congrArg D.categoryEquiv.functor.map hpre
  have hh : h = 0 := by
    simpa only [D.categoryEquiv.functor.map_preimage,
      D.categoryEquiv.functor.map_zero] using hmap
  apply (cancel_epi (D.objIso j).hom).1
  apply (cancel_mono (D.objIso i).inv).1
  simpa only [Category.assoc, zero_comp, comp_zero] using hh

/-- The chosen source preimage is an isomorphism exactly when the target
morphism is. -/
theorem isIso_undualMap_iff
    {i j : I}
    (g : tau.obj (D.labelEquiv j) ⟶ tau.obj (D.labelEquiv i)) :
    IsIso (QuotientSubmoduleEquidistribution.DualFixedSocleTransport.undualMap sigma tau D g) ↔
      IsIso g := by
  let h := (D.objIso j).hom ≫ g ≫ (D.objIso i).inv
  let q := D.categoryEquiv.functor.preimage h
  change IsIso q.unop ↔ IsIso g
  constructor
  · intro hqUnop
    letI : IsIso q.unop := hqUnop
    haveI : IsIso q := by
      simpa only [Quiver.Hom.op_unop] using
        (inferInstance : IsIso q.unop.op)
    haveI : IsIso (D.categoryEquiv.functor.map q) :=
      D.categoryEquiv.functor.map_isIso q
    haveI : IsIso h := by
      rw [← D.categoryEquiv.functor.map_preimage h]
      infer_instance
    let k := (D.objIso j).inv ≫ h ≫ (D.objIso i).hom
    haveI : IsIso k := by
      dsimp [k]
      infer_instance
    have hk : k = g := by
      simp only [k, h, Category.assoc, Iso.inv_hom_id_assoc,
        Iso.inv_hom_id, Category.comp_id]
    rw [← hk]
    infer_instance
  · intro hg
    letI : IsIso g := hg
    haveI : IsIso h := by
      dsimp [h]
      infer_instance
    haveI : IsIso (D.categoryEquiv.functor.map q) := by
      rw [D.categoryEquiv.functor.map_preimage]
      infer_instance
    haveI : IsIso q :=
      isIso_of_reflects_iso q D.categoryEquiv.functor
    infer_instance

/-- Any source Hom order gives a synchronized target Hom order by duality. -/
theorem dual_homOrderProperty [LinearOrder I]
    (H : HomOrderProperty sigma) :
    letI := dualLinearOrder sigma tau D
    HomOrderProperty tau := by
  letI := dualLinearOrder sigma tau D
  intro a b f hf hab
  obtain ⟨a, rfl⟩ := D.labelEquiv.surjective a
  obtain ⟨b, rfl⟩ := D.labelEquiv.surjective b
  let g : sigma.obj b ⟶ sigma.obj a :=
    QuotientSubmoduleEquidistribution.DualFixedSocleTransport.undualMap sigma tau D f
  have hg : g ≠ 0 := undualMap_ne_zero sigma tau D f hf
  have hne : b ≠ a := by
    intro h
    exact hab (congrArg D.labelEquiv h.symm)
  apply (dualLinearOrder_lt_iff sigma tau D _ _).2
  simpa only [Equiv.symm_apply_apply] using H g hg hne

/-- Reverse an explicit directed order through an aligned
anti-equivalence. -/
def reverseDirectedOrderChoice
    (E : DirectedOrderChoice sigma) : DirectedOrderChoice tau := by
  letI := E.order
  exact
    { order := dualLinearOrder sigma tau D
      homOrderProperty :=
        dual_homOrderProperty sigma tau D E.homOrderProperty }

/-- A strict Hom order, together with invertibility of every nonzero
indecomposable endomorphism, excludes all cycles of nonzero
nonisomorphisms. -/
theorem hasAcyclicNonzeroNonisomorphisms_of_homOrderProperty
    [LinearOrder I]
    (Horder : HomOrderProperty sigma)
    (Hendo : ∀ (i : I) (f : sigma.obj i ⟶ sigma.obj i),
      f ≠ 0 → IsIso f) :
    HasAcyclicNonzeroNonisomorphisms sigma := by
  intro i hcycle
  have hedge : ∀ {a b : I}, NonzeroNonisomorphism sigma a b → a < b := by
    intro a b hab
    obtain ⟨f, hf, hnotIso⟩ := hab
    have hne : a ≠ b := by
      intro h
      subst b
      exact hnotIso (Hendo a f hf)
    exact Horder f hf hne
  have hlt : Relation.TransGen (fun a b : I ↦ a < b) i i :=
    hcycle.lift id (fun _ _ h ↦ hedge h)
  have : i < i := by
    simpa only [Relation.transGen_eq_self] using hlt
  exact (lt_irrefl i) this

include D

/-- Nonzero indecomposable endomorphisms on the dual skeleton are invertible
whenever this holds on the source. -/
theorem dual_isIso_of_ne_zero_endomorphism
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (a : Kappa) (f : tau.obj a ⟶ tau.obj a) (hf : f ≠ 0) :
    IsIso f := by
  obtain ⟨i, rfl⟩ := D.labelEquiv.surjective a
  let g : sigma.obj i ⟶ sigma.obj i :=
    QuotientSubmoduleEquidistribution.DualFixedSocleTransport.undualMap sigma tau D f
  have hg : g ≠ 0 := undualMap_ne_zero sigma tau D f hf
  have hgIso : IsIso g := H.isIso_of_ne_zero_endomorphism sigma i g hg
  exact (isIso_undualMap_iff sigma tau D f).mp hgIso

/-- Representation-directed cycle-freeness transports across an aligned
anti-equivalence. -/
theorem dual_hasAcyclicNonzeroNonisomorphisms
    (H : HasAcyclicNonzeroNonisomorphisms sigma) :
    HasAcyclicNonzeroNonisomorphisms tau := by
  letI := directedLinearOrder sigma H
  letI := dualLinearOrder sigma tau D
  apply hasAcyclicNonzeroNonisomorphisms_of_homOrderProperty tau
  · exact dual_homOrderProperty sigma tau D
      (directedLinearOrder_homOrderProperty sigma H)
  · exact dual_isIso_of_ne_zero_endomorphism sigma tau D H

/-- The aligned anti-equivalence sends source projectives to target
injectives. -/
theorem injective_labelEquiv_iff_projective (i : I) :
    Injective (tau.obj (D.labelEquiv i)) ↔
      Projective (sigma.obj i) := by
  constructor
  · intro hTarget
    have hMap : Injective
        (D.categoryEquiv.functor.obj (Opposite.op (sigma.obj i))) :=
      Injective.of_iso (D.objIso i).symm hTarget
    have hOp : Injective (Opposite.op (sigma.obj i)) :=
      (D.categoryEquiv.map_injective_iff
        (Opposite.op (sigma.obj i))).mp hMap
    exact Injective.projective_iff_injective_op.mpr hOp
  · intro hSource
    have hOp : Injective (Opposite.op (sigma.obj i)) :=
      Injective.projective_iff_injective_op.mp hSource
    have hMap : Injective
        (D.categoryEquiv.functor.obj (Opposite.op (sigma.obj i))) :=
      (D.categoryEquiv.map_injective_iff
        (Opposite.op (sigma.obj i))).mpr hOp
    exact Injective.of_iso (D.objIso i) hMap

/-- Dually, source injectives become target projectives. -/
theorem projective_labelEquiv_iff_injective (i : I) :
    Projective (tau.obj (D.labelEquiv i)) ↔
      Injective (sigma.obj i) := by
  constructor
  · intro hTarget
    have hMap : Projective
        (D.categoryEquiv.functor.obj (Opposite.op (sigma.obj i))) :=
      Projective.of_iso (D.objIso i).symm hTarget
    have hOp : Projective (Opposite.op (sigma.obj i)) :=
      (D.categoryEquiv.map_projective_iff
        (Opposite.op (sigma.obj i))).mp hMap
    exact Injective.injective_iff_projective_op.mpr hOp
  · intro hSource
    have hOp : Projective (Opposite.op (sigma.obj i)) :=
      Injective.injective_iff_projective_op.mp hSource
    have hMap : Projective
        (D.categoryEquiv.functor.obj (Opposite.op (sigma.obj i))) :=
      (D.categoryEquiv.map_projective_iff
        (Opposite.op (sigma.obj i))).mpr hOp
    exact Projective.of_iso (D.objIso i) hMap

open DirectedAROrbit

/-- The source projective boundary is canonically the target injective
boundary under an aligned anti-equivalence. -/
def projectiveLabelEquivDualInjectiveLabel :
    ProjectiveLabel sigma ≃ InjectiveLabel tau where
  toFun p :=
    ⟨D.labelEquiv p.1,
      (injective_labelEquiv_iff_projective sigma tau D p.1).2 p.2⟩
  invFun q :=
    ⟨D.labelEquiv.symm q.1, by
      apply (injective_labelEquiv_iff_projective sigma tau D _).1
      simpa only [Equiv.apply_symm_apply] using q.2⟩
  left_inv p := by
    apply Subtype.ext
    exact D.labelEquiv.symm_apply_apply p.1
  right_inv q := by
    apply Subtype.ext
    exact D.labelEquiv.apply_symm_apply q.1

/-- The source injective boundary is canonically the target projective
boundary under an aligned anti-equivalence. -/
def injectiveLabelEquivDualProjectiveLabel :
    InjectiveLabel sigma ≃ ProjectiveLabel tau where
  toFun i :=
    ⟨D.labelEquiv i.1,
      (projective_labelEquiv_iff_injective sigma tau D i.1).2 i.2⟩
  invFun p :=
    ⟨D.labelEquiv.symm p.1, by
      apply (projective_labelEquiv_iff_injective sigma tau D _).1
      simpa only [Equiv.apply_symm_apply] using p.2⟩
  left_inv i := by
    apply Subtype.ext
    exact D.labelEquiv.symm_apply_apply i.1
  right_inv p := by
    apply Subtype.ext
    exact D.labelEquiv.apply_symm_apply p.1

omit D in
/-- Canonical increasing enumerations reverse exactly under a reverse
pullback order. -/
theorem canonicalPosition_reversePullback
    [Fintype I] [Fintype Kappa] [LinearOrder I]
    (e : Kappa ≃ I) (p : Fin (Fintype.card Kappa)) :
    letI := reversePullbackLinearOrder e
    e ((Fintype.orderIsoFinOfCardEq Kappa rfl) p) =
      (Fintype.orderIsoFinOfCardEq I rfl)
        (Fin.rev (finCongr (Fintype.card_congr e) p)) := by
  letI := reversePullbackLinearOrder e
  let source : Fin (Fintype.card I) ≃o I :=
    Fintype.orderIsoFinOfCardEq I rfl
  let label : Kappa ≃o OrderDual I :=
    { toEquiv := e
      map_rel_iff' := by intro x y; rfl }
  let reversed : Fin (Fintype.card Kappa) ≃o Kappa :=
    (Fin.castOrderIso (Fintype.card_congr e)).trans <|
      Fin.revOrderIso.symm.trans <| source.dual.trans label.symm
  have hEq : Fintype.orderIsoFinOfCardEq Kappa rfl = reversed :=
    Subsingleton.elim _ _
  rw [hEq]
  simp only [reversed, OrderIso.trans_apply, Fin.castOrderIso_apply,
    Fin.revOrderIso_symm_apply]
  exact e.apply_symm_apply _

end QuotientSubmoduleEquidistribution.RepresentationDirected.DualDirectedOrder
