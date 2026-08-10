import OpConjecture.RepresentationTheory.ExtDegreeNakayamaReduction
import OpConjecture.RepresentationTheory.TwoSourceExtBridge

/-!
# Ext forks from semisimple endpoint layers

For a short exact sequence with a finite-length indecomposable middle term,
every nonzero direct-summand component of either endpoint contributes a
nonzero component of its Yoneda `Ext¹` class.  Applied to two simple endpoint
summands, this gives the distinct-endpoint and parallel-arrow fork statements
needed in the first semisimple radical/top layers of the Nakayama reduction.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace OpConjecture.ExtForkSemisimpleLayers

universe u v

variable {R : Type u} [Ring R] [Small.{v} R]

/-- In an extension with indecomposable finite-length middle term, the
projection of the extension class onto a nonzero left direct summand of
the subobject endpoint cannot vanish. -/
theorem extClass_comp_biprod_fst_ne_zero
    {P Q T M : ModuleCat.{v} R}
    (hP : 𝟙 P ≠ 0) (hT : 𝟙 T ≠ 0)
    (f : P ⊞ Q ⟶ M) (g : M ⟶ T) (hfg : f ≫ g = 0)
    (hS : (ShortComplex.mk f g hfg).ShortExact)
    [IsNoetherian R M] [IsArtinian R M]
    (hM : OpConjecture.Foundation.IsIndecomposableModule R M) :
    hS.extClass.comp (Ext.mk₀ biprod.fst) (add_zero 1) ≠ 0 := by
  intro hzero
  let p : P ⊞ Q ⟶ P ⊞ Q := biprod.fst ≫ biprod.inl
  have hp_idem : p ≫ p = p := by
    dsimp [p]
    simp [Category.assoc]
  have hcompat :
      hS.extClass.comp (Ext.mk₀ p) (add_zero 1) =
        (Ext.mk₀ (0 : T ⟶ T)).comp hS.extClass (zero_add 1) := by
    dsimp [p]
    rw [← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_third_deg_zero,
      hzero, Ext.zero_comp, Ext.mk₀_zero, Ext.zero_comp]
  rcases
      OpConjecture.YonedaExtReflection.endpoint_idempotents_trivial_of_extClass_compatibility
        hS hM p (0 : T ⟶ T) hp_idem (by simp) hcompat with
    hzeroEnds | honeEnds
  · apply hP
    calc
      𝟙 P = biprod.inl ≫ p ≫ biprod.fst := by
        simp [p, Category.assoc]
      _ = biprod.inl ≫ (0 : P ⊞ Q ⟶ P ⊞ Q) ≫ biprod.fst := by
        rw [hzeroEnds.1]
      _ = 0 := by simp
  · exact hT honeEnds.2.symm

/-- The symmetric direct-summand component is also nonzero. -/
theorem extClass_comp_biprod_snd_ne_zero
    {P Q T M : ModuleCat.{v} R}
    (hQ : 𝟙 Q ≠ 0) (hT : 𝟙 T ≠ 0)
    (f : P ⊞ Q ⟶ M) (g : M ⟶ T) (hfg : f ≫ g = 0)
    (hS : (ShortComplex.mk f g hfg).ShortExact)
    [IsNoetherian R M] [IsArtinian R M]
    (hM : OpConjecture.Foundation.IsIndecomposableModule R M) :
    hS.extClass.comp (Ext.mk₀ biprod.snd) (add_zero 1) ≠ 0 := by
  intro hzero
  let p : P ⊞ Q ⟶ P ⊞ Q := biprod.snd ≫ biprod.inr
  have hp_idem : p ≫ p = p := by
    dsimp [p]
    simp [Category.assoc]
  have hcompat :
      hS.extClass.comp (Ext.mk₀ p) (add_zero 1) =
        (Ext.mk₀ (0 : T ⟶ T)).comp hS.extClass (zero_add 1) := by
    dsimp [p]
    rw [← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_third_deg_zero,
      hzero, Ext.zero_comp, Ext.mk₀_zero, Ext.zero_comp]
  rcases
      OpConjecture.YonedaExtReflection.endpoint_idempotents_trivial_of_extClass_compatibility
        hS hM p (0 : T ⟶ T) hp_idem (by simp) hcompat with
    hzeroEnds | honeEnds
  · apply hQ
    calc
      𝟙 Q = biprod.inr ≫ p ≫ biprod.snd := by
        simp [p, Category.assoc]
      _ = biprod.inr ≫ (0 : P ⊞ Q ⟶ P ⊞ Q) ≫ biprod.snd := by
        rw [hzeroEnds.1]
      _ = 0 := by simp
  · exact hT honeEnds.2.symm

/-- Dually, restricting an extension with indecomposable middle term to a
nonzero left direct summand of its quotient endpoint cannot vanish. -/
theorem biprod_inl_comp_extClass_ne_zero
    {J P Q M : ModuleCat.{v} R}
    (hJ : 𝟙 J ≠ 0) (hP : 𝟙 P ≠ 0)
    (f : J ⟶ M) (g : M ⟶ P ⊞ Q) (hfg : f ≫ g = 0)
    (hS : (ShortComplex.mk f g hfg).ShortExact)
    [IsNoetherian R M] [IsArtinian R M]
    (hM : OpConjecture.Foundation.IsIndecomposableModule R M) :
    (Ext.mk₀ biprod.inl).comp hS.extClass (zero_add 1) ≠ 0 := by
  intro hzero
  let p : P ⊞ Q ⟶ P ⊞ Q := biprod.fst ≫ biprod.inl
  have hp_idem : p ≫ p = p := by
    dsimp [p]
    simp [Category.assoc]
  have hcompat :
      hS.extClass.comp (Ext.mk₀ (0 : J ⟶ J)) (add_zero 1) =
        (Ext.mk₀ p).comp hS.extClass (zero_add 1) := by
    dsimp [p]
    rw [Ext.mk₀_zero, Ext.comp_zero, ← Ext.mk₀_comp_mk₀,
      Ext.comp_assoc_of_second_deg_zero, hzero, Ext.comp_zero]
  rcases
      OpConjecture.YonedaExtReflection.endpoint_idempotents_trivial_of_extClass_compatibility
        hS hM (0 : J ⟶ J) p (by simp) hp_idem hcompat with
    hzeroEnds | honeEnds
  · apply hP
    calc
      𝟙 P = biprod.inl ≫ p ≫ biprod.fst := by
        simp [p, Category.assoc]
      _ = biprod.inl ≫ (0 : P ⊞ Q ⟶ P ⊞ Q) ≫ biprod.fst := by
        rw [hzeroEnds.2]
      _ = 0 := by simp
  · exact hJ honeEnds.1.symm

/-- The right direct-summand restriction at the quotient endpoint is also
nonzero. -/
theorem biprod_inr_comp_extClass_ne_zero
    {J P Q M : ModuleCat.{v} R}
    (hJ : 𝟙 J ≠ 0) (hQ : 𝟙 Q ≠ 0)
    (f : J ⟶ M) (g : M ⟶ P ⊞ Q) (hfg : f ≫ g = 0)
    (hS : (ShortComplex.mk f g hfg).ShortExact)
    [IsNoetherian R M] [IsArtinian R M]
    (hM : OpConjecture.Foundation.IsIndecomposableModule R M) :
    (Ext.mk₀ biprod.inr).comp hS.extClass (zero_add 1) ≠ 0 := by
  intro hzero
  let p : P ⊞ Q ⟶ P ⊞ Q := biprod.snd ≫ biprod.inr
  have hp_idem : p ≫ p = p := by
    dsimp [p]
    simp [Category.assoc]
  have hcompat :
      hS.extClass.comp (Ext.mk₀ (0 : J ⟶ J)) (add_zero 1) =
        (Ext.mk₀ p).comp hS.extClass (zero_add 1) := by
    dsimp [p]
    rw [Ext.mk₀_zero, Ext.comp_zero, ← Ext.mk₀_comp_mk₀,
      Ext.comp_assoc_of_second_deg_zero, hzero, Ext.comp_zero]
  rcases
      OpConjecture.YonedaExtReflection.endpoint_idempotents_trivial_of_extClass_compatibility
        hS hM (0 : J ⟶ J) p (by simp) hp_idem hcompat with
    hzeroEnds | honeEnds
  · apply hQ
    calc
      𝟙 Q = biprod.inr ≫ p ≫ biprod.snd := by
        simp [p, Category.assoc]
      _ = biprod.inr ≫ (0 : P ⊞ Q ⟶ P ⊞ Q) ≫ biprod.snd := by
        rw [hzeroEnds.2]
      _ = 0 := by simp
  · exact hJ honeEnds.1.symm

section SkeletonSupport

variable {K A : Type u}
  [Field K] [IsAlgClosed K]
  [Ring A] [Small.{u} A] [IsNoetherianRing A] [IsArtinianRing A]
  [Algebra K A]
  {kappa : Type v} [Finite kappa]
  (tau : OpConjecture.IndecomposableSkeleton.{u, v, u} A kappa)

open OpConjecture.GabrielArrowBridge
open OpConjecture.ExtDegreeNakayamaReduction

omit [IsAlgClosed K] [IsArtinianRing A] [Finite kappa] in
/-- If the kernel of a short exact sequence is a direct sum of two
distinct chosen simples, indecomposability of the middle term forces two
distinct outgoing Ext--Gabriel arrows.  This is the precise first-radical-
layer fork argument: the two arrows are distinct because their targets are
the two distinct direct summands, not because of an arbitrary
composition-factor descent. -/
theorem outgoing_extGabrielFork_of_direct_sum_simple_kernel
    (hFinite : FiniteExtOneSupport (K := K) tau)
    (s p q : tau.SimpleIndex) (hpq : p ≠ q)
    {M : ModuleCat.{u} A}
    (f : (tau.obj p.1).obj ⊞ (tau.obj q.1).obj ⟶ M)
    (g : M ⟶ (tau.obj s.1).obj) (hfg : f ≫ g = 0)
    (hS : (ShortComplex.mk f g hfg).ShortExact)
    [IsNoetherian A M] [IsArtinian A M]
    (hM : OpConjecture.Foundation.IsIndecomposableModule A M) :
    ∃ a b : ExtGabrielArrowIndex (K := K) tau,
      a ≠ b ∧
        ExtGabrielArrowIndex.source tau a =
          ExtGabrielArrowIndex.source tau b := by
  letI : IsSimpleModule A (tau.obj p.1) :=
    (OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      (tau.obj p.1)).mp p.2
  letI : IsSimpleModule A (tau.obj q.1) :=
    (OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      (tau.obj q.1)).mp q.2
  letI : IsSimpleModule A (tau.obj s.1) :=
    (OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      (tau.obj s.1)).mp s.2
  letI : Simple (tau.obj p.1).obj :=
    (simple_iff_isSimpleModule' (tau.obj p.1).obj).mpr inferInstance
  letI : Simple (tau.obj q.1).obj :=
    (simple_iff_isSimpleModule' (tau.obj q.1).obj).mpr inferInstance
  letI : Simple (tau.obj s.1).obj :=
    (simple_iff_isSimpleModule' (tau.obj s.1).obj).mpr inferInstance
  letI : Nontrivial (tau.obj p.1) :=
    IsSimpleModule.nontrivial A (tau.obj p.1)
  letI : Nontrivial (tau.obj q.1) :=
    IsSimpleModule.nontrivial A (tau.obj q.1)
  letI : Nontrivial (tau.obj s.1) :=
    IsSimpleModule.nontrivial A (tau.obj s.1)
  let etaP : ExtOne tau s p :=
    hS.extClass.comp (Ext.mk₀ biprod.fst) (add_zero 1)
  let etaQ : ExtOne tau s q :=
    hS.extClass.comp (Ext.mk₀ biprod.snd) (add_zero 1)
  have hetaP : etaP ≠ 0 :=
    extClass_comp_biprod_fst_ne_zero
      (CategoryTheory.id_nonzero _) (CategoryTheory.id_nonzero _)
      f g hfg hS hM
  have hetaQ : etaQ ≠ 0 :=
    extClass_comp_biprod_snd_ne_zero
      (CategoryTheory.id_nonzero _) (CategoryTheory.id_nonzero _)
      f g hfg hS hM
  letI : FiniteDimensional K (ExtOne tau s p) :=
    hFinite s p
  letI : FiniteDimensional K (ExtOne tau s q) :=
    hFinite s q
  letI : Nontrivial (ExtOne tau s p) := ⟨etaP, 0, hetaP⟩
  letI : Nontrivial (ExtOne tau s q) := ⟨etaQ, 0, hetaQ⟩
  let a : ExtGabrielArrowIndex (K := K) tau :=
    ⟨s, p, ⟨0, Module.finrank_pos⟩⟩
  let b : ExtGabrielArrowIndex (K := K) tau :=
    ⟨s, q, ⟨0, Module.finrank_pos⟩⟩
  refine ⟨a, b, ?_, rfl⟩
  intro hab
  apply hpq
  exact congrArg (ExtGabrielArrowIndex.target tau) hab

omit [IsAlgClosed K] [IsArtinianRing A] [Finite kappa] in
/-- Dually, if the quotient of a short exact sequence is a direct sum of
two distinct chosen simples, indecomposability of the middle term forces
two distinct incoming Ext--Gabriel arrows. -/
theorem incoming_extGabrielFork_of_direct_sum_simple_quotient
    (hFinite : FiniteExtOneSupport (K := K) tau)
    (t p q : tau.SimpleIndex) (hpq : p ≠ q)
    {M : ModuleCat.{u} A}
    (f : (tau.obj t.1).obj ⟶ M)
    (g : M ⟶ (tau.obj p.1).obj ⊞ (tau.obj q.1).obj)
    (hfg : f ≫ g = 0)
    (hS : (ShortComplex.mk f g hfg).ShortExact)
    [IsNoetherian A M] [IsArtinian A M]
    (hM : OpConjecture.Foundation.IsIndecomposableModule A M) :
    ∃ a b : ExtGabrielArrowIndex (K := K) tau,
      a ≠ b ∧
        ExtGabrielArrowIndex.target tau a =
          ExtGabrielArrowIndex.target tau b := by
  letI : IsSimpleModule A (tau.obj p.1) :=
    (OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      (tau.obj p.1)).mp p.2
  letI : IsSimpleModule A (tau.obj q.1) :=
    (OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      (tau.obj q.1)).mp q.2
  letI : IsSimpleModule A (tau.obj t.1) :=
    (OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      (tau.obj t.1)).mp t.2
  letI : Simple (tau.obj p.1).obj :=
    (simple_iff_isSimpleModule' (tau.obj p.1).obj).mpr inferInstance
  letI : Simple (tau.obj q.1).obj :=
    (simple_iff_isSimpleModule' (tau.obj q.1).obj).mpr inferInstance
  letI : Simple (tau.obj t.1).obj :=
    (simple_iff_isSimpleModule' (tau.obj t.1).obj).mpr inferInstance
  letI : Nontrivial (tau.obj p.1) :=
    IsSimpleModule.nontrivial A (tau.obj p.1)
  letI : Nontrivial (tau.obj q.1) :=
    IsSimpleModule.nontrivial A (tau.obj q.1)
  letI : Nontrivial (tau.obj t.1) :=
    IsSimpleModule.nontrivial A (tau.obj t.1)
  let etaP : ExtOne tau p t :=
    (Ext.mk₀ biprod.inl).comp hS.extClass (zero_add 1)
  let etaQ : ExtOne tau q t :=
    (Ext.mk₀ biprod.inr).comp hS.extClass (zero_add 1)
  have hetaP : etaP ≠ 0 :=
    biprod_inl_comp_extClass_ne_zero
      (CategoryTheory.id_nonzero _) (CategoryTheory.id_nonzero _)
      f g hfg hS hM
  have hetaQ : etaQ ≠ 0 :=
    biprod_inr_comp_extClass_ne_zero
      (CategoryTheory.id_nonzero _) (CategoryTheory.id_nonzero _)
      f g hfg hS hM
  letI : FiniteDimensional K (ExtOne tau p t) :=
    hFinite p t
  letI : FiniteDimensional K (ExtOne tau q t) :=
    hFinite q t
  letI : Nontrivial (ExtOne tau p t) := ⟨etaP, 0, hetaP⟩
  letI : Nontrivial (ExtOne tau q t) := ⟨etaQ, 0, hetaQ⟩
  let a : ExtGabrielArrowIndex (K := K) tau :=
    ⟨p, t, ⟨0, Module.finrank_pos⟩⟩
  let b : ExtGabrielArrowIndex (K := K) tau :=
    ⟨q, t, ⟨0, Module.finrank_pos⟩⟩
  refine ⟨a, b, ?_, rfl⟩
  intro hab
  apply hpq
  exact congrArg (ExtGabrielArrowIndex.source tau) hab

omit [IsAlgClosed K] [IsArtinianRing A] [Finite kappa] in
/-- If the kernel consists of two copies of one chosen simple and the
quotient is simple, indecomposability forces the relevant `Ext¹` space to
have dimension at least two.  Hence the multiplicity-bearing quiver has two
parallel outgoing arrows. -/
theorem outgoing_parallel_extGabrielFork_of_two_simple_kernel
    (hFinite : FiniteExtOneSupport (K := K) tau)
    (s p : tau.SimpleIndex)
    {M : ModuleCat.{u} A}
    (f : (⨁ fun _ : Fin 2 ↦ (tau.obj p.1).obj) ⟶ M)
    (g : M ⟶ (⨁ fun _ : Unit ↦ (tau.obj s.1).obj))
    (hfg : f ≫ g = 0)
    (hS : (ShortComplex.mk f g hfg).ShortExact)
    [IsNoetherian A M] [IsArtinian A M]
    (hM : OpConjecture.Foundation.IsIndecomposableModule A M) :
    ∃ a b : ExtGabrielArrowIndex (K := K) tau,
      a ≠ b ∧
        ExtGabrielArrowIndex.source tau a =
          ExtGabrielArrowIndex.source tau b := by
  letI : IsSimpleModule A (tau.obj p.1) :=
    (OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      (tau.obj p.1)).mp p.2
  letI : IsSimpleModule A (tau.obj s.1) :=
    (OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      (tau.obj s.1)).mp s.2
  letI : Simple (tau.obj p.1).obj :=
    (simple_iff_isSimpleModule' (tau.obj p.1).obj).mpr inferInstance
  letI : Simple (tau.obj s.1).obj :=
    (simple_iff_isSimpleModule' (tau.obj s.1).obj).mpr inferInstance
  letI : FiniteDimensional K (ExtOne tau s p) := hFinite s p
  have hdim : 2 ≤ Module.finrank K (ExtOne tau s p) := by
    by_contra hnot
    have hle : Module.finrank K (ExtOne tau s p) ≤ 1 := by omega
    obtain ⟨ell, hell⟩ :=
      OpConjecture.YonedaExtReflection.exists_injective_linearMap_to_field_of_finrank_le_one
        hle
    let arrow : (Unit → K) →ₗ[K] (Fin 2 → K) :=
      OpConjecture.YonedaExtReflection.scalarizedExtLinearMap
        (tau.obj s.1).obj (tau.obj p.1).obj ell hS.extClass
    have harrow :
        OpConjecture.LoewyTwoRankCore.IsIdempotentIndecomposable arrow :=
      OpConjecture.YonedaExtReflection.shortExact_scalarizedExtLinearMap_isIdempotentIndecomposable
        (tau.obj s.1).obj (tau.obj p.1).obj M
        (CategoryTheory.id_nonzero _) (CategoryTheory.id_nonzero _)
        f g hfg hS hM ell hell
    have htarget : Module.finrank K (Fin 2 → K) ≤ 1 :=
      OpConjecture.LoewyTwoRankCore.target_finrank_le_one harrow
    simp at htarget
  have hzero : 0 < Module.finrank K (ExtOne tau s p) := by omega
  have hone : 1 < Module.finrank K (ExtOne tau s p) := by omega
  let a : ExtGabrielArrowIndex (K := K) tau :=
    ⟨s, p, ⟨0, hzero⟩⟩
  let b : ExtGabrielArrowIndex (K := K) tau :=
    ⟨s, p, ⟨1, hone⟩⟩
  refine ⟨a, b, ?_, rfl⟩
  intro hab
  have hindices :=
    congrArg
      (fun z : ExtGabrielArrowIndex (K := K) tau ↦ (z.2.2 : Nat))
      hab
  simp [a, b] at hindices

omit [IsAlgClosed K] [IsArtinianRing A] [Finite kappa] in
/-- The quotient-side companion: two copies of one simple in the quotient
force two parallel incoming arrows. -/
theorem incoming_parallel_extGabrielFork_of_two_simple_quotient
    (hFinite : FiniteExtOneSupport (K := K) tau)
    (t p : tau.SimpleIndex)
    {M : ModuleCat.{u} A}
    (f : (⨁ fun _ : Unit ↦ (tau.obj t.1).obj) ⟶ M)
    (g : M ⟶ (⨁ fun _ : Fin 2 ↦ (tau.obj p.1).obj))
    (hfg : f ≫ g = 0)
    (hS : (ShortComplex.mk f g hfg).ShortExact)
    [IsNoetherian A M] [IsArtinian A M]
    (hM : OpConjecture.Foundation.IsIndecomposableModule A M) :
    ∃ a b : ExtGabrielArrowIndex (K := K) tau,
      a ≠ b ∧
        ExtGabrielArrowIndex.target tau a =
          ExtGabrielArrowIndex.target tau b := by
  letI : IsSimpleModule A (tau.obj p.1) :=
    (OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      (tau.obj p.1)).mp p.2
  letI : IsSimpleModule A (tau.obj t.1) :=
    (OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      (tau.obj t.1)).mp t.2
  letI : Simple (tau.obj p.1).obj :=
    (simple_iff_isSimpleModule' (tau.obj p.1).obj).mpr inferInstance
  letI : Simple (tau.obj t.1).obj :=
    (simple_iff_isSimpleModule' (tau.obj t.1).obj).mpr inferInstance
  letI : FiniteDimensional K (ExtOne tau p t) := hFinite p t
  have hdim : 2 ≤ Module.finrank K (ExtOne tau p t) := by
    by_contra hnot
    have hle : Module.finrank K (ExtOne tau p t) ≤ 1 := by omega
    obtain ⟨ell, hell⟩ :=
      OpConjecture.YonedaExtReflection.exists_injective_linearMap_to_field_of_finrank_le_one
        hle
    let arrow : (Fin 2 → K) →ₗ[K] (Unit → K) :=
      OpConjecture.YonedaExtReflection.scalarizedExtLinearMap
        (tau.obj p.1).obj (tau.obj t.1).obj ell hS.extClass
    have harrow :
        OpConjecture.LoewyTwoRankCore.IsIdempotentIndecomposable arrow :=
      OpConjecture.YonedaExtReflection.shortExact_scalarizedExtLinearMap_isIdempotentIndecomposable
        (tau.obj p.1).obj (tau.obj t.1).obj M
        (CategoryTheory.id_nonzero _) (CategoryTheory.id_nonzero _)
        f g hfg hS hM ell hell
    have hsource : Module.finrank K (Fin 2 → K) ≤ 1 :=
      OpConjecture.LoewyTwoRankCore.source_finrank_le_one harrow
    simp at hsource
  have hzero : 0 < Module.finrank K (ExtOne tau p t) := by omega
  have hone : 1 < Module.finrank K (ExtOne tau p t) := by omega
  let a : ExtGabrielArrowIndex (K := K) tau :=
    ⟨p, t, ⟨0, hzero⟩⟩
  let b : ExtGabrielArrowIndex (K := K) tau :=
    ⟨p, t, ⟨1, hone⟩⟩
  refine ⟨a, b, ?_, rfl⟩
  intro hab
  have hindices :=
    congrArg
      (fun z : ExtGabrielArrowIndex (K := K) tau ↦ (z.2.2 : Nat))
      hab
  simp [a, b] at hindices

end SkeletonSupport

end OpConjecture.ExtForkSemisimpleLayers
