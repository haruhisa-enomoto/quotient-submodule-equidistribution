import OpConjecture.RepresentationDirected.RightAROccurrenceBasis
import OpConjecture.RepresentationTheory.FactorCategoryRadicalNilpotence
import OpConjecture.RepresentationTheory.FactorLadderRooted
import OpConjecture.RepresentationTheory.LocalARCofiniteTwoFormula

/-!
# Nonzero maps and irreducible reachability in finite representation type

For a finite complete indecomposable skeleton, the categorical radical is
nilpotent and every indecomposable has a minimal right almost-split map.
These two facts imply the standard radical-filtration statement that every
nonzero nonisomorphism between indecomposables determines a nonempty path of
irreducible arrows.

This is the bridge needed to pass from acyclicity of the Auslander--Reiten
quiver to representation-directedness.  It is independent of hereditary or
Dynkin classification arguments.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace OpConjecture.IndecomposableSkeleton

open OpConjecture.CategoricalIdeal

universe u v

variable {K R : Type u} [Field K] [Ring R] [Algebra K R]
  [FiniteDimensional K R] [IsNoetherianRing R]
  {ι : Type v} [Fintype ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

attribute [local instance] FintypeCat.fintype

namespace IrreducibleReachability

/-- The component of a map into the displayed indecomposable decomposition
of a right almost-split middle term. -/
def leftComponent {x y : ι}
    (A : σ.MinimalRightAlmostSplitDecomposition y)
    (g : σ.obj x ⟶ A.middle) (t : A.index) :
    σ.obj x ⟶ σ.obj (A.label t) :=
  g ≫ A.decomposition.hom ≫
    biproduct.π (fun j : A.index ↦ σ.obj (A.label j)) t

/-- The actual irreducible arrow from one displayed middle summand to the
right almost-split endpoint. -/
def rightComponent {y : ι}
    (A : σ.MinimalRightAlmostSplitDecomposition y) (t : A.index) :
    σ.obj (A.label t) ⟶ σ.obj y :=
  biproduct.ι (fun j : A.index ↦ σ.obj (A.label j)) t ≫
    A.decomposition.inv ≫ A.map

omit [Fintype ι] in
/-- Expanding through the displayed middle decomposition writes a factor
through the right almost-split map as the sum of its component composites. -/
theorem sum_leftComponent_comp_rightComponent {x y : ι}
    (A : σ.MinimalRightAlmostSplitDecomposition y)
    (g : σ.obj x ⟶ A.middle) :
    (∑ t : A.index,
        leftComponent σ A g t ≫ rightComponent σ A t) =
      g ≫ A.map := by
  let F : A.index → FGModuleCat.{u} R :=
    fun t ↦ σ.obj (A.label t)
  have hlift :
      biproduct.lift (fun t ↦ leftComponent σ A g t) =
        g ≫ A.decomposition.hom := by
    apply biproduct.hom_ext
    intro t
    simp [leftComponent, Category.assoc]
  have hdesc :
      biproduct.desc (fun t ↦ rightComponent σ A t) =
        A.decomposition.inv ≫ A.map := by
    apply biproduct.hom_ext'
    intro t
    simp [rightComponent]
  rw [← biproduct.lift_desc, hlift, hdesc]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

omit [Fintype ι] in
/-- If a factor through a minimal right almost-split map escapes the next
radical power, one of its indecomposable source components already escapes
the preceding power. -/
theorem exists_leftComponent_not_mem_pow {x y : ι}
    (Q : OpConjecture.CategoricalRadical.NilpotentRadicalData
      (FGModuleCat.{u} R))
    (A : σ.MinimalRightAlmostSplitDecomposition y)
    (f : σ.obj x ⟶ σ.obj y)
    (g : σ.obj x ⟶ A.middle) (hgf : g ≫ A.map = f)
    (n : ℕ)
    (hf : f ∉ (Q.ideal.pow (n + 1)).hom (σ.obj x) (σ.obj y)) :
    ∃ t : A.index,
      leftComponent σ A g t ∉
        (Q.ideal.pow n).hom (σ.obj x) (σ.obj (A.label t)) := by
  classical
  by_contra hall
  push Not at hall
  apply hf
  rw [← hgf, ← sum_leftComponent_comp_rightComponent σ A g]
  apply AddSubgroup.sum_mem
  intro t ht
  rw [Q.ideal.pow_succ]
  apply HomIdeal.comp_mem_mul (hall t)
  apply (Q.mem_ideal_iff (rightComponent σ A t)).2
  apply (σ.isRadicalMorphism_iff_not_isSplitMono_from_obj _).2
  exact
    (rightARSummandArrow_irreducible
      (sigma := σ) A t).not_isSplitMono

/-- Escaping the `(n+1)`st radical power produces a nonempty irreducible
path.  The induction peels off the terminal irreducible component of a
minimal right almost-split map. -/
theorem transGen_irreducibleEdge_of_mem_radical_not_mem_pow_succ
    (D : σ.TwoSidedLocalARData)
    (Q : OpConjecture.CategoricalRadical.NilpotentRadicalData
      (FGModuleCat.{u} R)) :
    ∀ n : ℕ, ∀ {x y : ι} (f : σ.obj x ⟶ σ.obj y),
      OpConjecture.CategoricalRadical.IsRadicalMorphism f →
      f ∉ (Q.ideal.pow (n + 1)).hom (σ.obj x) (σ.obj y) →
      Relation.TransGen σ.irreducibleEdge x y
  | 0, x, y, f, hfrad, hf => by
      exact (hf (by
        simpa only [Q.ideal.pow_one] using
          (Q.mem_ideal_iff f).2 hfrad)).elim
  | n + 1, x, y, f, hfrad, hf => by
      let A := D.chosenRightARAt σ y
      obtain ⟨g, hgf⟩ := A.rightAlmostSplit.factors f (by
        exact (σ.isRadicalMorphism_iff_not_isSplitEpi_to_obj f).1 hfrad)
      obtain ⟨t, ht⟩ := exists_leftComponent_not_mem_pow
        σ Q A f g hgf (n + 1) hf
      let a : σ.obj x ⟶ σ.obj (A.label t) :=
        leftComponent σ A g t
      have hedge : σ.irreducibleEdge (A.label t) y := by
        exact ⟨rightComponent σ A t,
          rightARSummandArrow_irreducible (sigma := σ) A t⟩
      by_cases ha :
          OpConjecture.CategoricalRadical.IsRadicalMorphism a
      · have hpath : Relation.TransGen σ.irreducibleEdge x (A.label t) :=
          transGen_irreducibleEdge_of_mem_radical_not_mem_pow_succ
            D Q n a ha (by simpa [a] using ht)
        exact Relation.TransGen.tail hpath hedge
      · have hasplit : IsSplitMono a := by
          rw [σ.isRadicalMorphism_iff_not_isSplitMono_from_obj] at ha
          exact Classical.byContradiction ha
        letI : IsSplitMono a := hasplit
        have hxy : x = A.label t := by
          letI : IsSplitEpi a :=
            σ.isSplitEpi_of_isSplitMono_between_obj a
          letI : IsIso a := isIso_of_epi_of_isSplitMono a
          exact σ.eq_of_iso ⟨asIso a⟩
        subst x
        exact Relation.TransGen.single hedge
termination_by n => n

/-- In finite representation type, every nonzero nonisomorphism between
chosen indecomposables gives a nonempty path in the irreducible AR digraph. -/
theorem transGen_irreducibleEdge_of_nonzeroNonisomorphism
    (D : σ.TwoSidedLocalARData)
    (Q : OpConjecture.CategoricalRadical.NilpotentRadicalData
      (FGModuleCat.{u} R))
    {x y : ι}
    (h : OpConjecture.RepresentationDirected.NonzeroNonisomorphism σ x y) :
    Relation.TransGen σ.irreducibleEdge x y := by
  obtain ⟨f, hfzero, hfiso⟩ := h
  have hfrad : OpConjecture.CategoricalRadical.IsRadicalMorphism f := by
    apply (σ.isRadicalMorphism_iff_not_isSplitEpi_to_obj f).2
    intro hsplit
    letI : IsSplitEpi f := hsplit
    letI : IsSplitMono f :=
      σ.isSplitMono_of_isSplitEpi_between_obj f
    exact hfiso (isIso_of_epi_of_isSplitMono f)
  obtain ⟨N, hN⟩ := Q.nilpotent
  have hfN : f ∉ (Q.ideal.pow N).hom (σ.obj x) (σ.obj y) := by
    rw [hN]
    simpa using hfzero
  have hNpos : N ≠ 0 := by
    intro hzero
    subst N
    apply hfN
    rw [Q.ideal.pow_zero]
    exact AddSubgroup.mem_top f
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hNpos
  exact transGen_irreducibleEdge_of_mem_radical_not_mem_pow_succ
    σ D Q n f hfrad hfN

/-- Acyclicity of the irreducible AR digraph implies the exact
representation-directed cycle-freeness condition once the radical is
nilpotent and local right almost-split decompositions are available. -/
theorem hasAcyclicNonzeroNonisomorphisms_of_irreducibleEdge_acyclic
    (D : σ.TwoSidedLocalARData)
    (Q : OpConjecture.CategoricalRadical.NilpotentRadicalData
      (FGModuleCat.{u} R))
    (hacyclic : ∀ x : ι,
      ¬ Relation.TransGen σ.irreducibleEdge x x) :
    OpConjecture.RepresentationDirected.HasAcyclicNonzeroNonisomorphisms σ := by
  intro x hcycle
  apply hacyclic x
  have lift : ∀ {a b : ι},
      Relation.TransGen
          (OpConjecture.RepresentationDirected.NonzeroNonisomorphism σ)
          a b →
        Relation.TransGen σ.irreducibleEdge a b := by
    intro a b hab
    induction hab with
    | single h =>
        exact transGen_irreducibleEdge_of_nonzeroNonisomorphism σ D Q h
    | @tail b c hab hbc ih =>
        exact Relation.TransGen.trans ih
          (transGen_irreducibleEdge_of_nonzeroNonisomorphism σ D Q hbc)
  exact lift hcycle

include K in
/-- The canonical nilpotent categorical radical on finitely generated
modules over a finite-dimensional representation-finite algebra. -/
def finiteDimensionalFgNilpotentRadicalData :
    OpConjecture.CategoricalRadical.NilpotentRadicalData
      (FGModuleCat.{u} R) := by
  letI (i : ι) : Module K (σ.obj i) :=
    Module.restrictScalars K R (σ.obj i)
  letI (i : ι) : IsScalarTower K R (σ.obj i) :=
    IsScalarTower.restrictScalars K R (σ.obj i)
  letI (i : ι) : FiniteDimensional K (σ.obj i) :=
    Module.Finite.trans R (σ.obj i)
  let G :=
    OpConjecture.AuslanderEquivalence.FiniteTypeGenerator.additiveGenerator σ
  letI : IsArtinianRing (End G) :=
    OpConjecture.IndecomposableSkeleton.LegalQuotientDeletionChain.isArtinianRing_skeletonAuslanderAlgebra
      (K := K) σ
  exact
    OpConjecture.CategoricalRadical.nilpotentRadicalDataOfArtinianGenerator
      G
      (OpConjecture.AuslanderEquivalence.FiniteTypeGenerator.additiveGenerator_isFiniteAddGenerator
        σ)

include K in
/-- Finite-dimensional specialization: acyclicity of the irreducible AR
digraph already implies the manuscript's cycle-freeness condition for all
nonzero nonisomorphisms. -/
theorem finiteDimensional_hasAcyclicNonzeroNonisomorphisms_of_irreducibleEdge_acyclic
    (hacyclic : ∀ x : ι,
      ¬ Relation.TransGen σ.irreducibleEdge x x) :
    OpConjecture.RepresentationDirected.HasAcyclicNonzeroNonisomorphisms σ :=
  hasAcyclicNonzeroNonisomorphisms_of_irreducibleEdge_acyclic σ
    (σ.finiteDimensionalTwoSidedLocalARData K R)
    (finiteDimensionalFgNilpotentRadicalData (K := K) σ)
    hacyclic

end IrreducibleReachability

end OpConjecture.IndecomposableSkeleton
