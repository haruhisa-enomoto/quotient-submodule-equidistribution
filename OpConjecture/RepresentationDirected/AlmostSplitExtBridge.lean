import OpConjecture.RepresentationTheory.AlmostSplitExtNonvanishing

/-!
# The almost-split Ext bridge in directed effective lifting

The manuscript's effective-lifting argument invokes Auslander--Reiten
duality only to turn a nonzero `Ext¹(X,Z)` class into a nonzero map
`Z -> tau X`.  The representation-theoretic file
`AlmostSplitExtNonvanishing` proves that weaker implication directly from a
right almost-split sequence.

This file records its exact directed consumer.  A nonzero map `X -> Z`, the
resulting nonzero map `Z -> tau X`, and one mesh segment
`tau X -> E -> X` contradict a directed Hom order.  The same argument proves
the lifting statement actually used in the induction.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace OpConjecture.RepresentationDirected

universe uC vC w

section PullbackClass

variable {C : Type uC} [Category.{vC} C] [Abelian C] [HasExt.{w} C]

/-- A morphism which does not lift through the quotient map of a short exact
sequence has a nonzero pulled-back extension class. -/
theorem pullback_extClass_ne_zero_of_not_lifts
    {S : ShortComplex C} (hS : S.ShortExact)
    {X : C} (a : X ⟶ S.X₃)
    (hnot : ¬ ∃ b : X ⟶ S.X₂, b ≫ S.g = a) :
    (Ext.mk₀ a).comp hS.extClass (zero_add 1) ≠ 0 := by
  intro hzero
  apply hnot
  obtain ⟨b, hb⟩ :=
    Ext.covariant_sequence_exact₃
      (X := X) hS (Ext.mk₀ a)
      (rfl : 0 + 1 = 1) hzero
  refine ⟨Ext.addEquiv₀ b, ?_⟩
  apply (Ext.mk₀_bijective X S.X₃).1
  rw [← Ext.mk₀_comp_mk₀]
  simpa using hb

end PullbackClass

universe uR uIota

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {Iota : Type uIota} [Preorder Iota]
  (sigma : IndecomposableSkeleton.{uR, uIota, uR} R Iota)

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- The two consequences of a directed ordering used in the Hom--Ext
contradiction.  They are exactly the weak and strict inequalities supplied
by the manuscript's order by nonzero nonisomorphisms. -/
structure DirectedHomOrder : Prop where
  le_of_nonzero :
    ∀ {i j : Iota} (f : sigma.obj i ⟶ sigma.obj j), f ≠ 0 → i ≤ j
  lt_of_irreducible :
    ∀ {i j : Iota},
      HasIrreducibleMorphism (sigma.obj i) (sigma.obj j) → i < j

namespace DirectedHomOrder

variable {sigma} [HasExt.{uR} (FGModuleCat.{uR} R)]

omit [Preorder Iota] [HasExt.{uR} (FGModuleCat.{uR} R)] in
/-- The chosen minimal right almost-split middle at a nonprojective object
has at least one indecomposable coordinate.  Otherwise its displayed finite
biproduct decomposition would make the middle zero; epimorphy of the
almost-split map would then make its indecomposable target zero. -/
theorem chosenRightAR_index_nonempty
    (D : sigma.FiniteARTranslationData)
    (x : sigma.NonprojectiveLabel) :
    Nonempty (D.chosenRightAR sigma x).index := by
  classical
  let A := D.chosenRightAR sigma x
  letI : Epi A.map :=
    OpConjecture.IndecomposableSkeleton.IsRightAlmostSplit.epi_of_not_projective_obj
      sigma A.map A.rightAlmostSplit x.2
  have htarget : ¬ IsZero (sigma.obj x.1) := by
    intro hzero
    let U := forget₂ (FGModuleCat.{uR} R) (ModuleCat.{uR} R)
    have hzero' : IsZero (U.obj (sigma.obj x.1)) := U.map_isZero hzero
    have hsub : Subsingleton (sigma.obj x.1) :=
      ModuleCat.isZero_iff_subsingleton.mp hzero'
    exact not_nontrivial_iff_subsingleton.mpr hsub
      (sigma.indecomposable x.1).nontrivial
  have hmiddle : ¬ IsZero A.middle := by
    intro hzero
    exact htarget (IsZero.of_epi A.map hzero)
  by_contra hindex
  have hsum : IsZero (sigma.sumOver A.index A.label) := by
    refine
      { unique_to := fun X => ⟨⟨⟨0⟩, ?_⟩⟩
        unique_from := fun X => ⟨⟨⟨0⟩, ?_⟩⟩ }
    · intro f
      apply biproduct.hom_ext'
      intro t
      exact (hindex ⟨t⟩).elim
    · intro f
      apply biproduct.hom_ext
      intro t
      exact (hindex ⟨t⟩).elim
  exact hmiddle (hsum.of_iso A.decomposition)

/-- A nonzero map `X -> Z`, nonzero `Ext¹(X,Z)`, and one irreducible mesh
segment `tau X -> E -> X` are incompatible with a directed Hom order. -/
theorem ext_eq_zero_of_nonzero_hom_of_ar_incidence
    {D : sigma.FiniteARTranslationData}
    (H : DirectedHomOrder sigma)
    (x : sigma.NonprojectiveLabel) (z e : Iota)
    (a : sigma.obj x.1 ⟶ sigma.obj z) (ha : a ≠ 0)
    (hTauE : HasIrreducibleMorphism
      (sigma.obj (D.arTranslation sigma x).1) (sigma.obj e))
    (hEX : HasIrreducibleMorphism (sigma.obj e) (sigma.obj x.1))
    (xi : Ext (sigma.obj x.1) (sigma.obj z) 1) :
    xi = 0 := by
  by_contra hxi
  obtain ⟨b, hb⟩ :=
    D.exists_ne_zero_hom_to_arTranslation_of_ext_ne_zero
      sigma x (sigma.obj z) xi hxi
  have hxz : x.1 ≤ z := H.le_of_nonzero a ha
  have hzTau : z ≤ (D.arTranslation sigma x).1 :=
    H.le_of_nonzero b hb
  have hTauE' : (D.arTranslation sigma x).1 < e :=
    H.lt_of_irreducible hTauE
  have hEX' : e < x.1 := H.lt_of_irreducible hEX
  exact (not_lt_of_ge (hxz.trans hzTau)) (hTauE'.trans hEX')

/-- Paper-facing lifting form of the same contradiction.  If `X -> Z` is
nonzero and `tau X -> E -> X` is one irreducible mesh segment, then every map
from `X` to the quotient of a short exact sequence starting at `Z` lifts to
its middle term. -/
theorem exists_lift_of_nonzero_kernel_hom_of_ar_incidence
    {D : sigma.FiniteARTranslationData}
    (H : DirectedHomOrder sigma)
    (x : sigma.NonprojectiveLabel) (z e : Iota)
    (g : sigma.obj x.1 ⟶ sigma.obj z) (hg : g ≠ 0)
    (hTauE : HasIrreducibleMorphism
      (sigma.obj (D.arTranslation sigma x).1) (sigma.obj e))
    (hEX : HasIrreducibleMorphism (sigma.obj e) (sigma.obj x.1))
    {V W : FGModuleCat.{uR} R}
    {j : sigma.obj z ⟶ V} {p : V ⟶ W} {hjp : j ≫ p = 0}
    (hS : (ShortComplex.mk j p hjp).ShortExact)
    (a : sigma.obj x.1 ⟶ W) :
    ∃ b : sigma.obj x.1 ⟶ V, b ≫ p = a := by
  by_contra hnot
  have hclass :
      (Ext.mk₀ a).comp hS.extClass (zero_add 1) ≠ 0 :=
    pullback_extClass_ne_zero_of_not_lifts hS a hnot
  exact hclass
    (H.ext_eq_zero_of_nonzero_hom_of_ar_incidence
      x z e g hg hTauE hEX
      ((Ext.mk₀ a).comp hS.extClass (zero_add 1)))

/-- Choosing one coordinate of the minimal right almost-split middle term
supplies both irreducible arrows required by the directed lifting lemma. -/
theorem exists_lift_of_nonzero_kernel_hom_of_middle_index
    {D : sigma.FiniteARTranslationData}
    (H : DirectedHomOrder sigma)
    (x : sigma.NonprojectiveLabel) (z : Iota)
    (t : (D.chosenRightAR sigma x).index)
    (g : sigma.obj x.1 ⟶ sigma.obj z) (hg : g ≠ 0)
    {V W : FGModuleCat.{uR} R}
    {j : sigma.obj z ⟶ V} {p : V ⟶ W} {hjp : j ≫ p = 0}
    (hS : (ShortComplex.mk j p hjp).ShortExact)
    (a : sigma.obj x.1 ⟶ W) :
    ∃ b : sigma.obj x.1 ⟶ V, b ≫ p = a := by
  let A := D.chosenRightAR sigma x
  let e : Iota := A.label t
  have hEX :
      HasIrreducibleMorphism (sigma.obj e) (sigma.obj x.1) :=
    (A.summandIrreducibleCorrespondence e).1 ⟨t, rfl⟩
  have hTauE :
      HasIrreducibleMorphism
        (sigma.obj (D.arTranslation sigma x).1) (sigma.obj e) :=
    (D.arTranslation_incidence sigma x e).1 hEX
  exact H.exists_lift_of_nonzero_kernel_hom_of_ar_incidence
    x z e g hg hTauE hEX hS a

/-- The exact almost-split contradiction needed in directed effective
lifting, with the mesh coordinate selected automatically. -/
theorem exists_lift_of_nonzero_kernel_hom
    {D : sigma.FiniteARTranslationData}
    (H : DirectedHomOrder sigma)
    (x : sigma.NonprojectiveLabel) (z : Iota)
    (g : sigma.obj x.1 ⟶ sigma.obj z) (hg : g ≠ 0)
    {V W : FGModuleCat.{uR} R}
    {j : sigma.obj z ⟶ V} {p : V ⟶ W} {hjp : j ≫ p = 0}
    (hS : (ShortComplex.mk j p hjp).ShortExact)
    (a : sigma.obj x.1 ⟶ W) :
    ∃ b : sigma.obj x.1 ⟶ V, b ≫ p = a := by
  let t := Classical.choice (chosenRightAR_index_nonempty D x)
  exact H.exists_lift_of_nonzero_kernel_hom_of_middle_index
    x z t g hg hS a

end DirectedHomOrder

end OpConjecture.RepresentationDirected
