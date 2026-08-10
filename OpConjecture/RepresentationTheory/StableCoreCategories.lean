import OpConjecture.RepresentationTheory.StableQuotients
import OpConjecture.RepresentationTheory.RingelCoreAdapter
import Mathlib.CategoryTheory.InducedCategory

/-!
# Ringel's stable torsionless and cotorsionless categories

The ambient quotient categories are restricted to the concrete
`Sub(projectiveGenerator)` and `Fac(injectiveCogenerator)` objects used by
the faithful cores.  We also form their chosen nonboundary skeletons and
show that an equivalence of those stable skeleton categories produces
exactly the `RingelEtaStableData` required by the cardinality theorem.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Set

namespace OpConjecture.RingelStable

universe u v

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {iota : Type v} [Finite iota]
  (sigma : OpConjecture.IndecomposableSkeleton.{u, v, u} R iota)

namespace FaithfulCoreAdapter

open OpConjecture.IndecomposableSkeleton.FaithfulCore

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-! ## Full stable categories -/

/-- Ringel's source-faithful torsionless predicate: a finite module
embeds into a finite projective module. -/
def Torsionless (X : FGModuleCat.{u} R) : Prop :=
  ∃ (P : FGModuleCat.{u} R) (f : X ⟶ P), Projective P ∧ Mono f

/-- Ringel's source-faithful cotorsionless predicate: a finite module is
a factor module of a finite injective module. -/
def Cotorsionless (X : FGModuleCat.{u} R) : Prop :=
  ∃ (I : FGModuleCat.{u} R) (f : I ⟶ X), Injective I ∧ Epi f

omit [IsNoetherianRing R] in
/-- Torsionlessness is invariant under isomorphism. -/
theorem torsionless_of_iso
    {X Y : FGModuleCat.{u} R} (e : X ≅ Y)
    (hX : Torsionless X) : Torsionless Y := by
  obtain ⟨P, f, hP, hf⟩ := hX
  letI : Mono f := hf
  exact ⟨P, e.inv ≫ f, hP, inferInstance⟩

omit [IsNoetherianRing R] in
/-- Cotorsionlessness is invariant under isomorphism. -/
theorem cotorsionless_of_iso
    {X Y : FGModuleCat.{u} R} (e : X ≅ Y)
    (hX : Cotorsionless X) : Cotorsionless Y := by
  obtain ⟨I, f, hI, hf⟩ := hX
  letI : Epi f := hf
  exact ⟨I, f ≫ e.hom, hI, inferInstance⟩

omit [IsNoetherianRing R] in
/-- Concrete `Sub(G)` membership is torsionlessness whenever `G` is
projective. -/
theorem torsionless_of_inSubOfModule
    {G X : FGModuleCat.{u} R} (hG : Projective G)
    (hX : OpConjecture.IndecomposableSkeleton.InSubOfModule G X) :
    Torsionless X := by
  obtain ⟨L, m, hm⟩ := hX
  have hsum : Projective (⨁ fun _ : L ↦ G) := by
    letI : Projective G := hG
    constructor
    intro E Y f e _
    choose lift hlift using fun t : L ↦
      Projective.factors
        (biproduct.ι (fun _ : L ↦ G) t ≫ f) e
    refine ⟨biproduct.desc lift, ?_⟩
    apply biproduct.hom_ext'
    intro t
    simpa only [biproduct.ι_desc_assoc] using hlift t
  exact ⟨⨁ fun _ : L ↦ G, m, hsum, hm⟩

omit [IsNoetherianRing R] in
/-- Concrete `Fac(J)` membership is cotorsionlessness whenever `J` is
injective. -/
theorem cotorsionless_of_inFacOfModule
    {J X : FGModuleCat.{u} R} (hJ : Injective J)
    (hX : OpConjecture.IndecomposableSkeleton.InFacOfModule J X) :
    Cotorsionless X := by
  obtain ⟨L, p, hp⟩ := hX
  letI (_ : L) : Injective J := hJ
  exact ⟨⨁ fun _ : L ↦ J, p, inferInstance, hp⟩

/-- The object property defining Ringel's torsionless category `L(R)`
inside the projective-stable category. -/
def torsionlessStableProperty :
    ObjectProperty (ProjectiveStableCategory (R := R)) :=
  fun X ↦ Torsionless X.as

/-- Ringel's `L(R)/P(R)`, realized as the full subcategory of the
projective-stable quotient on torsionless modules. -/
abbrev TorsionlessStableCategory :=
  (torsionlessStableProperty (R := R)).FullSubcategory

/-- The object property defining Ringel's cotorsionless category `K(R)`
inside the injective-stable category. -/
def cotorsionlessStableProperty :
    ObjectProperty (InjectiveStableCategory (R := R)) :=
  fun X ↦ Cotorsionless X.as

/-- Ringel's `K(R)/Q(R)`, realized as the full subcategory of the
injective-stable quotient on cotorsionless modules. -/
abbrev CotorsionlessStableCategory :=
  (cotorsionlessStableProperty (R := R)).FullSubcategory

/-- Torsionlessness as an object property of finite modules. -/
def torsionlessModuleProperty : ObjectProperty (FGModuleCat.{u} R) :=
  fun X ↦ Torsionless X

/-- Cotorsionlessness as an object property of finite modules. -/
def cotorsionlessModuleProperty : ObjectProperty (FGModuleCat.{u} R) :=
  fun X ↦ Cotorsionless X

instance torsionlessModuleProperty_isoClosed :
    (torsionlessModuleProperty (R := R)).IsClosedUnderIsomorphisms where
  of_iso e h := torsionless_of_iso (R := R) e h

instance cotorsionlessModuleProperty_isoClosed :
    (cotorsionlessModuleProperty (R := R)).IsClosedUnderIsomorphisms where
  of_iso e h := cotorsionless_of_iso (R := R) e h

/-- The ordinary full category `L(R)` of finite torsionless modules. -/
abbrev TorsionlessModuleCategory :=
  (torsionlessModuleProperty (R := R)).FullSubcategory

/-- The ordinary full category `K(R)` of finite cotorsionless modules. -/
abbrev CotorsionlessModuleCategory :=
  (cotorsionlessModuleProperty (R := R)).FullSubcategory

/-- The canonical quotient functor `L(R) ⟶ L(R)/P(R)`. -/
def torsionlessStableQuotientFunctor :
    TorsionlessModuleCategory (R := R) ⥤
      TorsionlessStableCategory (R := R) where
  obj X := ⟨(projectiveStableFunctor (R := R)).obj X.obj, X.property⟩
  map f := ObjectProperty.homMk
    ((projectiveStableFunctor (R := R)).map f.hom)
  map_id X := by
    apply ObjectProperty.hom_ext
    exact (projectiveStableFunctor (R := R)).map_id X.obj
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact (projectiveStableFunctor (R := R)).map_comp f.hom g.hom

/-- The canonical quotient functor `K(R) ⟶ K(R)/Q(R)`. -/
def cotorsionlessStableQuotientFunctor :
    CotorsionlessModuleCategory (R := R) ⥤
      CotorsionlessStableCategory (R := R) where
  obj X := ⟨(injectiveStableFunctor (R := R)).obj X.obj, X.property⟩
  map f := ObjectProperty.homMk
    ((injectiveStableFunctor (R := R)).map f.hom)
  map_id X := by
    apply ObjectProperty.hom_ext
    exact (injectiveStableFunctor (R := R)).map_id X.obj
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact (injectiveStableFunctor (R := R)).map_comp f.hom g.hom

omit [IsNoetherianRing R] in
/-- Equality under `L(R) ⟶ L(R)/P(R)` is exactly factorization of
the difference through a finite projective module. -/
theorem torsionlessStableQuotientFunctor_map_eq_iff
    {X Y : TorsionlessModuleCategory (R := R)} (f g : X ⟶ Y) :
    (torsionlessStableQuotientFunctor (R := R)).map f =
        (torsionlessStableQuotientFunctor (R := R)).map g ↔
      Nonempty (FactorsThroughProjective (f.hom - g.hom)) := by
  constructor
  · intro h
    apply (projectiveStable_map_eq_iff f.hom g.hom).1
    exact congrArg (fun q ↦ q.hom) h
  · intro h
    apply ObjectProperty.hom_ext
    exact (projectiveStable_map_eq_iff f.hom g.hom).2 h

omit [IsNoetherianRing R] in
/-- Equality under `K(R) ⟶ K(R)/Q(R)` is exactly factorization of
the difference through a finite injective module. -/
theorem cotorsionlessStableQuotientFunctor_map_eq_iff
    {X Y : CotorsionlessModuleCategory (R := R)} (f g : X ⟶ Y) :
    (cotorsionlessStableQuotientFunctor (R := R)).map f =
        (cotorsionlessStableQuotientFunctor (R := R)).map g ↔
      Nonempty (FactorsThroughInjective (f.hom - g.hom)) := by
  constructor
  · intro h
    apply (injectiveStable_map_eq_iff f.hom g.hom).1
    exact congrArg (fun q ↦ q.hom) h
  · intro h
    apply ObjectProperty.hom_ext
    exact (injectiveStable_map_eq_iff f.hom g.hom).2 h

/-! ## Chosen nonboundary stable skeletons -/

/-- Nonprojective torsionless labels in the chosen indecomposable
skeleton. -/
abbrev TorsionlessNonprojectiveLabels :=
  {i // i ∈ (submoduleCore sigma : Set iota) \ projectiveSet sigma}

/-- Noninjective cotorsionless labels in the chosen indecomposable
skeleton. -/
abbrev CotorsionlessNoninjectiveLabels :=
  {i // i ∈ (quotientCore sigma : Set iota) \ injectiveSet sigma}

omit [Finite iota] in
/-- A nonprojective torsionless label as an object of `L/P`. -/
def torsionlessStableLabelObject
    (i : TorsionlessNonprojectiveLabels sigma) :
    TorsionlessStableCategory (R := R) :=
  ⟨(projectiveStableFunctor (R := R)).obj (sigma.obj i.1), by
    obtain ⟨P⟩ := i.2.1
    letI (t : P.index) : Projective (sigma.obj (P.label t)) :=
      P.mem t
    have hsum : Projective (sigma.sumOver P.index P.label) := by
      constructor
      intro E Y f e _
      choose lift hlift using fun t : P.index ↦
        Projective.factors
          (biproduct.ι (fun t : P.index ↦ sigma.obj (P.label t)) t ≫ f) e
      refine ⟨biproduct.desc lift, ?_⟩
      apply biproduct.hom_ext'
      intro t
      simpa only [biproduct.ι_desc_assoc] using hlift t
    exact ⟨sigma.sumOver P.index P.label, P.map, hsum, P.mono⟩⟩

omit [Finite iota] in
/-- A noninjective cotorsionless label as an object of `K/Q`. -/
def cotorsionlessStableLabelObject
    (i : CotorsionlessNoninjectiveLabels sigma) :
    CotorsionlessStableCategory (R := R) :=
  ⟨(injectiveStableFunctor (R := R)).obj (sigma.obj i.1), by
    obtain ⟨P⟩ := i.2.1
    letI (t : P.index) : Injective (sigma.obj (P.label t)) :=
      P.mem t
    exact ⟨sigma.sumOver P.index P.label, P.map, inferInstance, P.epi⟩⟩

/-- The induced projective-stable category on the chosen nonprojective
torsionless labels.  Its objects are literally the relevant label
subtype, and its homs are the quotient homs. -/
abbrev TorsionlessStableSkeleton :=
  InducedCategory (TorsionlessStableCategory (R := R))
    (torsionlessStableLabelObject sigma)

/-- The induced injective-stable category on the chosen noninjective
cotorsionless labels. -/
abbrev CotorsionlessStableSkeleton :=
  InducedCategory (CotorsionlessStableCategory (R := R))
    (cotorsionlessStableLabelObject sigma)

/-- Inclusion of the chosen torsionless stable skeleton into the ambient
projective-stable category. -/
def torsionlessStableSkeletonInclusion :
    TorsionlessStableSkeleton sigma ⥤
      ProjectiveStableCategory (R := R) :=
  inducedFunctor (torsionlessStableLabelObject sigma) ⋙
    (torsionlessStableProperty (R := R)).ι

/-- Inclusion of the chosen cotorsionless stable skeleton into the
ambient injective-stable category. -/
def cotorsionlessStableSkeletonInclusion :
    CotorsionlessStableSkeleton sigma ⥤
      InjectiveStableCategory (R := R) :=
  inducedFunctor (cotorsionlessStableLabelObject sigma) ⋙
    (cotorsionlessStableProperty (R := R)).ι

/-! ## From a categorical equivalence to the counting datum -/

/-- The exact categorical seam left by Ringel's construction after
restricting `D η` to chosen nonboundary indecomposable representatives. -/
abbrev RingelReducedStableEquivalence :=
  TorsionlessStableSkeleton sigma ≌
    CotorsionlessStableSkeleton sigma

/-- A categorical equivalence of the chosen nonboundary stable
skeletons supplies the forward/backward label maps and its unit/counit
supply the required inverse identities modulo projectives/injectives. -/
def etaStableDataOfReducedEquivalence
    (E : RingelReducedStableEquivalence sigma) :
    RingelEtaStableData sigma where
  forward := fun x ↦ E.functor.obj x
  backward := fun y ↦ E.inverse.obj y
  source_inverse_stable := fun x ↦
    stableIsoOfQuotientIso
      ((torsionlessStableSkeletonInclusion sigma).mapIso
        (E.unitIso.app x).symm)
  target_inverse_stable := fun y ↦
    injectiveStableIsoOfQuotientIso
      ((cotorsionlessStableSkeletonInclusion sigma).mapIso
        (E.counitIso.app y))

/-- Consequently a reduced stable equivalence is already sufficient for
the exact faithful-core cardinality proposition. -/
theorem ringelCoreCardinality_of_reducedStableEquivalence
    [IsNoetherianRing Rᵐᵒᵖ]
    (K : Type u) [Field K] [Algebra K R] [FiniteDimensional K R]
    (E : RingelReducedStableEquivalence sigma) :
    RingelCoreCardinality sigma :=
  ringelCoreCardinality_of_etaStableData sigma K
    (etaStableDataOfReducedEquivalence sigma E)

end FaithfulCoreAdapter

end OpConjecture.RingelStable
