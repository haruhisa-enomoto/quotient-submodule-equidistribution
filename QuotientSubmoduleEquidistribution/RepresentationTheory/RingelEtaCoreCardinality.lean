import QuotientSubmoduleEquidistribution.RepresentationTheory.RingelEtaComposition
import QuotientSubmoduleEquidistribution.RepresentationTheory.StableCoreCategories

/-!
# From Ringel's stable equivalence to faithful-core cardinality

Ringel's ambient equivalence `Dη : L(R)/P(R) ≃ K(R)/Q(R)` need not send a
chosen indecomposable module to a literally indecomposable representative:
the quasi-inverses used in the quotient equivalences may add stable-zero
summands.  This file removes those summands inside the ordinary finite module
category.

For an indecomposable nonboundary finite module, Fitting's theorem makes every
idempotent in its stable endomorphism ring equal to zero or one.  This property
passes through an equivalence.  A finite indecomposable decomposition of the
image therefore has a surviving nonboundary summand whose coordinate
projection is the identity in the stable quotient.  Choosing such summands in both
directions gives the exact `RingelEtaStableData` used by the faithful-core
counting theorem.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.RingelStable

universe u v

variable {R : Type u} [Ring R]

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

private theorem fg_end_pow_hom
    {X : FGModuleCat.{u} R} (f : X ⟶ X) (n : ℕ) :
    ((CategoryTheory.End.of f) ^ n : End X).hom.hom =
      f.hom.hom ^ n := by
  induction n with
  | zero =>
      ext x
      rfl
  | succ n ih =>
      rw [pow_succ, pow_succ, CategoryTheory.End.mul_def]
      change
        ((CategoryTheory.End.of f) ^ n).hom.hom.comp f.hom.hom =
          (f.hom.hom ^ n).comp f.hom.hom
      rw [ih]

theorem projective_iff_isZero_projectiveStable
    (X : FGModuleCat.{u} R) :
    Projective X ↔
      IsZero ((projectiveStableFunctor (R := R)).obj X) := by
  constructor
  · intro hX
    rw [IsZero.iff_id_eq_zero]
    rw [← (projectiveStableFunctor (R := R)).map_id X,
      ← (projectiveStableFunctor (R := R)).map_zero]
    apply (projectiveStable_map_eq_iff (𝟙 X) 0).2
    exact ⟨{
      middle := X
      projective := hX
      left := 𝟙 X
      right := 𝟙 X
      fac := by simp }⟩
  · intro hX
    have hEq :
        (projectiveStableFunctor (R := R)).map (𝟙 X) =
          (projectiveStableFunctor (R := R)).map 0 := by
      rw [(projectiveStableFunctor (R := R)).map_id,
        (projectiveStableFunctor (R := R)).map_zero]
      exact (IsZero.iff_id_eq_zero _).1 hX
    obtain ⟨hfac⟩ :=
      (projectiveStable_map_eq_iff (𝟙 X) 0).1 hEq
    apply projective_of_isUnit_of_factorsThroughProjective
      (f := 𝟙 X)
    · simpa using hfac
    · exact isUnit_one

theorem injective_iff_isZero_injectiveStable
    (X : FGModuleCat.{u} R) :
    Injective X ↔
      IsZero ((injectiveStableFunctor (R := R)).obj X) := by
  constructor
  · intro hX
    rw [IsZero.iff_id_eq_zero]
    rw [← (injectiveStableFunctor (R := R)).map_id X,
      ← (injectiveStableFunctor (R := R)).map_zero]
    apply (injectiveStable_map_eq_iff (𝟙 X) 0).2
    exact ⟨{
      middle := X
      injective := hX
      left := 𝟙 X
      right := 𝟙 X
      fac := by simp }⟩
  · intro hX
    have hEq :
        (injectiveStableFunctor (R := R)).map (𝟙 X) =
          (injectiveStableFunctor (R := R)).map 0 := by
      rw [(injectiveStableFunctor (R := R)).map_id,
        (injectiveStableFunctor (R := R)).map_zero]
      exact (IsZero.iff_id_eq_zero _).1 hX
    obtain ⟨hfac⟩ :=
      (injectiveStable_map_eq_iff (𝟙 X) 0).1 hEq
    apply injective_of_isUnit_of_factorsThroughInjective
      (f := 𝟙 X)
    · simpa using hfac
    · exact isUnit_one

theorem projectiveStable_idempotent_eq_zero_or_id
    (X : FGModuleCat.{u} R)
    (hXindec : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R X)
    (hXfinite : IsFiniteLength R X)
    (a : End ((projectiveStableFunctor (R := R)).obj X))
    (ha : a ≫ a = a) :
    a = 0 ∨ a = 𝟙 _ := by
  letI : IsNoetherian R X :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hXfinite).1
  letI : IsArtinian R X :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hXfinite).2
  let f : X ⟶ X :=
    (projectiveStableFunctor (R := R)).preimage a
  have hmap : (projectiveStableFunctor (R := R)).map f = a :=
    (projectiveStableFunctor (R := R)).map_preimage a
  have haIdem : IsIdempotentElem a := by
    change a ≫ a = a
    exact ha
  by_cases hf : IsUnit f.hom.hom
  · right
    have hbij : Function.Bijective f.hom.hom :=
      (Module.End.isUnit_iff f.hom.hom).1 hf
    let U := forget₂ (FGModuleCat R) (ModuleCat R)
    letI : IsIso (U.map f) := by
      change IsIso f.hom
      exact (ConcreteCategory.isIso_iff_bijective f.hom).2 hbij
    letI : IsIso f := isIso_of_reflects_iso f U
    haveI : IsIso a := by
      rw [← hmap]
      infer_instance
    exact
      (IsIdempotentElem.iff_eq_one_of_isUnit
        ((CategoryTheory.isUnit_iff_isIso a).2 inferInstance)).1 haIdem
  · left
    have hnil : IsNilpotent f.hom.hom :=
      (hXindec.isNilpotent_iff_not_isUnit f.hom.hom).2 hf
    have hnilCat : IsNilpotent (CategoryTheory.End.of f) := by
      obtain ⟨n, hn⟩ := hnil
      refine ⟨n, ?_⟩
      apply FGModuleCat.hom_ext
      rw [fg_end_pow_hom]
      exact hn
    have hnilMap : IsNilpotent a := by
      obtain ⟨n, hn⟩ := hnilCat
      refine ⟨n, ?_⟩
      rw [← hmap]
      calc
        ((projectiveStableFunctor (R := R)).mapEnd X)
              (CategoryTheory.End.of f) ^ n =
            (projectiveStableFunctor (R := R)).map
              ((CategoryTheory.End.of f) ^ n) := by
          exact
            ((projectiveStableFunctor (R := R)).mapEnd X).map_pow
              (CategoryTheory.End.of f) n |>.symm
        _ = (projectiveStableFunctor (R := R)).map 0 :=
          congrArg
            (fun g : End X ↦
              (projectiveStableFunctor (R := R)).map g) hn
        _ = 0 := by
          exact (projectiveStableFunctor (R := R)).map_zero X X
    exact haIdem.eq_zero_of_isNilpotent hnilMap

theorem injectiveStable_idempotent_eq_zero_or_id
    (X : FGModuleCat.{u} R)
    (hXindec : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R X)
    (hXfinite : IsFiniteLength R X)
    (a : End ((injectiveStableFunctor (R := R)).obj X))
    (ha : a ≫ a = a) :
    a = 0 ∨ a = 𝟙 _ := by
  letI : IsNoetherian R X :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hXfinite).1
  letI : IsArtinian R X :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hXfinite).2
  let f : X ⟶ X :=
    (injectiveStableFunctor (R := R)).preimage a
  have hmap : (injectiveStableFunctor (R := R)).map f = a :=
    (injectiveStableFunctor (R := R)).map_preimage a
  have haIdem : IsIdempotentElem a := by
    change a ≫ a = a
    exact ha
  by_cases hf : IsUnit f.hom.hom
  · right
    have hbij : Function.Bijective f.hom.hom :=
      (Module.End.isUnit_iff f.hom.hom).1 hf
    let U := forget₂ (FGModuleCat R) (ModuleCat R)
    letI : IsIso (U.map f) := by
      change IsIso f.hom
      exact (ConcreteCategory.isIso_iff_bijective f.hom).2 hbij
    letI : IsIso f := isIso_of_reflects_iso f U
    haveI : IsIso a := by
      rw [← hmap]
      infer_instance
    exact
      (IsIdempotentElem.iff_eq_one_of_isUnit
        ((CategoryTheory.isUnit_iff_isIso a).2 inferInstance)).1 haIdem
  · left
    have hnil : IsNilpotent f.hom.hom :=
      (hXindec.isNilpotent_iff_not_isUnit f.hom.hom).2 hf
    have hnilCat : IsNilpotent (CategoryTheory.End.of f) := by
      obtain ⟨n, hn⟩ := hnil
      refine ⟨n, ?_⟩
      apply FGModuleCat.hom_ext
      rw [fg_end_pow_hom]
      exact hn
    have hnilMap : IsNilpotent a := by
      obtain ⟨n, hn⟩ := hnilCat
      refine ⟨n, ?_⟩
      rw [← hmap]
      calc
        ((injectiveStableFunctor (R := R)).mapEnd X)
              (CategoryTheory.End.of f) ^ n =
            (injectiveStableFunctor (R := R)).map
              ((CategoryTheory.End.of f) ^ n) := by
          exact
            ((injectiveStableFunctor (R := R)).mapEnd X).map_pow
              (CategoryTheory.End.of f) n |>.symm
        _ = (injectiveStableFunctor (R := R)).map 0 :=
          congrArg
            (fun g : End X ↦
              (injectiveStableFunctor (R := R)).map g) hn
        _ = 0 := by
          exact (injectiveStableFunctor (R := R)).map_zero X X
    exact haIdem.eq_zero_of_isNilpotent hnilMap

private def biproductCoordinateEnd
    {n : ℕ} (A : Fin n → FGModuleCat.{u} R)
    {Y : FGModuleCat.{u} R} (e : Y ≅ ⨁ A) (t : Fin n) :
    Y ⟶ Y :=
  e.hom ≫ biproduct.π A t ≫ biproduct.ι A t ≫ e.inv

private theorem biproductCoordinateEnd_idempotent
    {n : ℕ} (A : Fin n → FGModuleCat.{u} R)
    {Y : FGModuleCat.{u} R} (e : Y ≅ ⨁ A) (t : Fin n) :
    biproductCoordinateEnd A e t ≫
        biproductCoordinateEnd A e t =
      biproductCoordinateEnd A e t := by
  simp [biproductCoordinateEnd, Category.assoc]

private theorem biproductCoordinateEnd_ne_zero_injectiveStable
    {n : ℕ} (A : Fin n → FGModuleCat.{u} R)
    {Y : FGModuleCat.{u} R} (e : Y ≅ ⨁ A) (t : Fin n)
    (ht : ¬ Injective (A t)) :
    (injectiveStableFunctor (R := R)).map
        (biproductCoordinateEnd A e t) ≠ 0 := by
  let inc : A t ⟶ Y := biproduct.ι A t ≫ e.inv
  let proj : Y ⟶ A t := e.hom ≫ biproduct.π A t
  intro hzero
  have hzeroObj :
      IsZero ((injectiveStableFunctor (R := R)).obj (A t)) := by
    rw [IsZero.iff_id_eq_zero]
    calc
      𝟙 ((injectiveStableFunctor (R := R)).obj (A t)) =
          (injectiveStableFunctor (R := R)).map (𝟙 (A t)) := by
        rw [(injectiveStableFunctor (R := R)).map_id]
      _ = (injectiveStableFunctor (R := R)).map
          (inc ≫ biproductCoordinateEnd A e t ≫ proj) := by
        apply congrArg
        simp [inc, proj, biproductCoordinateEnd, Category.assoc]
      _ =
          (injectiveStableFunctor (R := R)).map inc ≫
            (injectiveStableFunctor (R := R)).map
              (biproductCoordinateEnd A e t) ≫
                (injectiveStableFunctor (R := R)).map proj := by
        simp only [Functor.map_comp]
      _ = 0 := by rw [hzero]; simp
  exact ht ((injective_iff_isZero_injectiveStable (A t)).2 hzeroObj)

private theorem biproductCoordinateEnd_ne_zero_projectiveStable
    {n : ℕ} (A : Fin n → FGModuleCat.{u} R)
    {Y : FGModuleCat.{u} R} (e : Y ≅ ⨁ A) (t : Fin n)
    (ht : ¬ Projective (A t)) :
    (projectiveStableFunctor (R := R)).map
        (biproductCoordinateEnd A e t) ≠ 0 := by
  let inc : A t ⟶ Y := biproduct.ι A t ≫ e.inv
  let proj : Y ⟶ A t := e.hom ≫ biproduct.π A t
  intro hzero
  have hzeroObj :
      IsZero ((projectiveStableFunctor (R := R)).obj (A t)) := by
    rw [IsZero.iff_id_eq_zero]
    calc
      𝟙 ((projectiveStableFunctor (R := R)).obj (A t)) =
          (projectiveStableFunctor (R := R)).map (𝟙 (A t)) := by
        rw [(projectiveStableFunctor (R := R)).map_id]
      _ = (projectiveStableFunctor (R := R)).map
          (inc ≫ biproductCoordinateEnd A e t ≫ proj) := by
        apply congrArg
        simp [inc, proj, biproductCoordinateEnd, Category.assoc]
      _ =
          (projectiveStableFunctor (R := R)).map inc ≫
            (projectiveStableFunctor (R := R)).map
              (biproductCoordinateEnd A e t) ≫
                (projectiveStableFunctor (R := R)).map proj := by
        simp only [Functor.map_comp]
      _ = 0 := by rw [hzero]; simp
  exact ht ((projective_iff_isZero_projectiveStable (A t)).2 hzeroObj)

namespace FaithfulCoreAdapter

open QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore

variable [IsNoetherianRing R]
  {iota : Type v} [Finite iota]
  (sigma : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, v, u} R iota)

omit [Finite iota] in
/-- Every finite projective object belongs to the additive closure of the
chosen indecomposable projective labels. -/
theorem inAdd_projectiveLabels_of_projective
    (P : FGModuleCat.{u} R) (hP : Projective P) :
    sigma.InAdd (projectiveLabels sigma) P := by
  classical
  letI : Projective P := hP
  obtain ⟨n, a, ⟨e⟩⟩ := sigma.decomposes P
  refine ⟨{
    index := FintypeCat.of (Fin n)
    label := a
    mem := ?_
    iso := e }⟩
  intro t
  let r : Retract (sigma.obj (a t)) P :=
    { i :=
        biproduct.ι (fun j : Fin n ↦ sigma.obj (a j)) t ≫ e.inv
      r :=
        e.hom ≫
          biproduct.π (fun j : Fin n ↦ sigma.obj (a j)) t
      retract := by simp }
  exact r.projective

/-- A chosen noninjective indecomposable representative of an object in
the cotorsionless stable category. -/
structure InjectiveStableRepresentative
    (Y : CotorsionlessStableCategory (R := R)) where
  label : iota
  mem_core : label ∈ (quotientCore sigma : Set iota)
  noninjective : ¬ Injective (sigma.obj label)
  iso :
    (injectiveStableFunctor (R := R)).obj (sigma.obj label) ≅ Y.obj

/-- A chosen nonprojective indecomposable representative of an object in
the torsionless stable category. -/
structure ProjectiveStableRepresentative
    (X : TorsionlessStableCategory (R := R)) where
  label : iota
  mem_core : label ∈ (submoduleCore sigma : Set iota)
  nonprojective : ¬ Projective (sigma.obj label)
  iso :
    (projectiveStableFunctor (R := R)).obj (sigma.obj label) ≅ X.obj

omit [Finite iota] in
set_option backward.isDefEq.respectTransparency false in
/-- A nonzero cotorsionless stable object whose endomorphisms have no
nontrivial idempotents is represented by a noninjective summand of
any finite indecomposable decomposition. -/
theorem injectiveStableRepresentative_nonempty
    (Y : CotorsionlessStableCategory (R := R))
    (hY : ¬ IsZero Y.obj)
    (hIdem : ∀ a : End Y.obj, a ≫ a = a →
      a = 0 ∨ a = 𝟙 Y.obj) :
    Nonempty (InjectiveStableRepresentative sigma Y) := by
  classical
  obtain ⟨n, a, ⟨e⟩⟩ := sigma.decomposes Y.obj.as
  let A : Fin n → FGModuleCat.{u} R := fun t ↦ sigma.obj (a t)
  have hex : ∃ t : Fin n, ¬ Injective (A t) := by
    by_contra hall
    push Not at hall
    letI (t : Fin n) : Injective (A t) := hall t
    have hsum : Injective (⨁ A) := inferInstance
    have hYinj : Injective Y.obj.as :=
      Injective.of_iso e.symm hsum
    exact hY ((injective_iff_isZero_injectiveStable Y.obj.as).1 hYinj)
  obtain ⟨t, ht⟩ := hex
  let c : Y.obj.as ⟶ Y.obj.as :=
    biproductCoordinateEnd A e t
  have hcIdem : c ≫ c = c :=
    biproductCoordinateEnd_idempotent A e t
  let qc : End Y.obj :=
    (injectiveStableFunctor (R := R)).map c
  have hqcIdem : qc ≫ qc = qc := by
    dsimp [qc]
    rw [← (injectiveStableFunctor (R := R)).map_comp, hcIdem]
  have hqcNonzero : qc ≠ 0 := by
    exact biproductCoordinateEnd_ne_zero_injectiveStable A e t ht
  have hqcOne : qc = 𝟙 Y.obj :=
    (hIdem qc hqcIdem).resolve_left hqcNonzero
  let inc : A t ⟶ Y.obj.as := biproduct.ι A t ≫ e.inv
  let proj : Y.obj.as ⟶ A t := e.hom ≫ biproduct.π A t
  let stableIso :
      (injectiveStableFunctor (R := R)).obj (A t) ≅ Y.obj :=
    { hom := (injectiveStableFunctor (R := R)).map inc
      inv := (injectiveStableFunctor (R := R)).map proj
      hom_inv_id := by
        rw [← (injectiveStableFunctor (R := R)).map_comp]
        simp [inc, proj, Category.assoc]
      inv_hom_id := by
        change
          (injectiveStableFunctor (R := R)).map (proj ≫ inc) =
            𝟙 Y.obj
        simpa [c, qc, proj, inc, biproductCoordinateEnd,
          Category.assoc] using hqcOne }
  have hcore : a t ∈ (quotientCore sigma : Set iota) := by
    obtain ⟨I, p, hI, hp⟩ := Y.property
    letI : Epi p := hp
    have hIadd : sigma.InAdd (injectiveLabels sigma) I :=
      inAdd_injectiveLabels_of_injective sigma I hI
    have hIfac : sigma.InFac (injectiveLabels sigma) I :=
      QuotientSubmoduleEquidistribution.IndecomposableSkeleton.inFac_of_inAdd sigma hIadd
    letI : Epi (p ≫ proj) := inferInstance
    change sigma.InFac (injectiveLabels sigma) (sigma.obj (a t))
    exact sigma.inFac_of_epi hIfac (p ≫ proj)
  exact ⟨{
    label := a t
    mem_core := hcore
    noninjective := ht
    iso := stableIso }⟩

omit [Finite iota] in
set_option backward.isDefEq.respectTransparency false in
/-- The projective-stable analogue of
`injectiveStableRepresentative_nonempty`. -/
theorem projectiveStableRepresentative_nonempty
    (X : TorsionlessStableCategory (R := R))
    (hX : ¬ IsZero X.obj)
    (hIdem : ∀ a : End X.obj, a ≫ a = a →
      a = 0 ∨ a = 𝟙 X.obj) :
    Nonempty (ProjectiveStableRepresentative sigma X) := by
  classical
  obtain ⟨n, a, ⟨e⟩⟩ := sigma.decomposes X.obj.as
  let A : Fin n → FGModuleCat.{u} R := fun t ↦ sigma.obj (a t)
  have hex : ∃ t : Fin n, ¬ Projective (A t) := by
    by_contra hall
    push Not at hall
    letI (t : Fin n) : Projective (A t) := hall t
    have hsum : Projective (⨁ A) := by
      constructor
      intro E Y f p hp
      choose lift hlift using fun t : Fin n ↦
        Projective.factors (biproduct.ι A t ≫ f) p
      refine ⟨biproduct.desc lift, ?_⟩
      apply biproduct.hom_ext'
      intro t
      simpa only [biproduct.ι_desc_assoc] using hlift t
    have hXproj : Projective X.obj.as :=
      Projective.of_iso e.symm hsum
    exact hX ((projective_iff_isZero_projectiveStable X.obj.as).1 hXproj)
  obtain ⟨t, ht⟩ := hex
  let c : X.obj.as ⟶ X.obj.as :=
    biproductCoordinateEnd A e t
  have hcIdem : c ≫ c = c :=
    biproductCoordinateEnd_idempotent A e t
  let qc : End X.obj :=
    (projectiveStableFunctor (R := R)).map c
  have hqcIdem : qc ≫ qc = qc := by
    dsimp [qc]
    rw [← (projectiveStableFunctor (R := R)).map_comp, hcIdem]
  have hqcNonzero : qc ≠ 0 :=
    biproductCoordinateEnd_ne_zero_projectiveStable A e t ht
  have hqcOne : qc = 𝟙 X.obj :=
    (hIdem qc hqcIdem).resolve_left hqcNonzero
  let inc : A t ⟶ X.obj.as := biproduct.ι A t ≫ e.inv
  let proj : X.obj.as ⟶ A t := e.hom ≫ biproduct.π A t
  let stableIso :
      (projectiveStableFunctor (R := R)).obj (A t) ≅ X.obj :=
    { hom := (projectiveStableFunctor (R := R)).map inc
      inv := (projectiveStableFunctor (R := R)).map proj
      hom_inv_id := by
        rw [← (projectiveStableFunctor (R := R)).map_comp]
        simp [inc, proj, Category.assoc]
      inv_hom_id := by
        change
          (projectiveStableFunctor (R := R)).map (proj ≫ inc) =
            𝟙 X.obj
        simpa [c, qc, proj, inc, biproductCoordinateEnd,
          Category.assoc] using hqcOne }
  have hcore : a t ∈ (submoduleCore sigma : Set iota) := by
    obtain ⟨P, m, hP, hm⟩ := X.property
    letI : Mono m := hm
    have hPadd : sigma.InAdd (projectiveLabels sigma) P :=
      inAdd_projectiveLabels_of_projective sigma P hP
    have hPsub : sigma.InSub (projectiveLabels sigma) P :=
      QuotientSubmoduleEquidistribution.IndecomposableSkeleton.inSub_of_inAdd sigma hPadd
    letI : Mono (inc ≫ m) := inferInstance
    change sigma.InSub (projectiveLabels sigma) (sigma.obj (a t))
    exact sigma.inSub_of_mono hPsub (inc ≫ m)
  exact ⟨{
    label := a t
    mem_core := hcore
    nonprojective := ht
    iso := stableIso }⟩

private theorem equivalence_target_idempotent_eq_zero_or_id
    {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D]
    {P : ObjectProperty C} {Q : ObjectProperty D}
    (E : P.FullSubcategory ≌ Q.FullSubcategory)
    [E.functor.PreservesZeroMorphisms]
    (X : P.FullSubcategory)
    (hX : ∀ a : End X.obj, a ≫ a = a →
      a = 0 ∨ a = 𝟙 X.obj)
    (a : End (E.functor.obj X).obj)
    (ha : a ≫ a = a) :
    a = 0 ∨ a = 𝟙 (E.functor.obj X).obj := by
  let a' : End (E.functor.obj X) := ObjectProperty.homMk a
  let b' : End X := E.functor.preimage a'
  have hb' : b' ≫ b' = b' := by
    apply E.functor.map_injective
    rw [E.functor.map_comp]
    apply ObjectProperty.hom_ext
    simp only [b', Functor.map_preimage,
      ObjectProperty.FullSubcategory.comp_hom]
    change a ≫ a = a
    exact ha
  have hb : b'.hom ≫ b'.hom = b'.hom :=
    congrArg (fun z ↦ z.hom) hb'
  rcases hX b'.hom hb with hb0 | hb1
  · left
    have hb'0 : b' = 0 := by
      apply ObjectProperty.hom_ext
      exact hb0
    have ha'0 : a' = 0 := by
      calc
        a' = E.functor.map b' := (E.functor.map_preimage a').symm
        _ = E.functor.map 0 := congrArg E.functor.map hb'0
        _ = 0 := E.functor.map_zero _ _
    exact congrArg (fun z ↦ z.hom) ha'0
  · right
    have hb'1 : b' = 𝟙 X := by
      apply ObjectProperty.hom_ext
      exact hb1
    have ha'1 : a' = 𝟙 (E.functor.obj X) := by
      calc
        a' = E.functor.map b' := (E.functor.map_preimage a').symm
        _ = E.functor.map (𝟙 X) := congrArg E.functor.map hb'1
        _ = 𝟙 (E.functor.obj X) := E.functor.map_id X
    exact congrArg (fun z ↦ z.hom) ha'1

private theorem equivalence_obj_not_isZero
    {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D]
    {P : ObjectProperty C} {Q : ObjectProperty D}
    (E : P.FullSubcategory ≌ Q.FullSubcategory)
    [E.functor.PreservesZeroMorphisms]
    (X : P.FullSubcategory)
    (hX : ¬ IsZero X.obj) :
    ¬ IsZero (E.functor.obj X).obj := by
  intro hEX
  apply hX
  rw [IsZero.iff_id_eq_zero]
  have hmap :
      E.functor.map (𝟙 X) = E.functor.map 0 := by
    rw [E.functor.map_id, E.functor.map_zero]
    apply ObjectProperty.hom_ext
    exact (IsZero.iff_id_eq_zero _).1 hEX
  exact congrArg (fun z ↦ z.hom) (E.functor.map_injective hmap)

omit [Finite iota] in
/-- The chosen target representative of `E` on one nonprojective
torsionless skeleton label. -/
noncomputable def forwardStableRepresentative
    (E : TorsionlessStableCategory (R := R) ≌
      CotorsionlessStableCategory (R := R))
    (x : TorsionlessNonprojectiveLabels sigma) :
    InjectiveStableRepresentative sigma
      (E.functor.obj (torsionlessStableLabelObject sigma x)) := by
  let X := torsionlessStableLabelObject sigma x
  have hX : ¬ IsZero X.obj := by
    intro hzero
    exact x.property.2
      ((projective_iff_isZero_projectiveStable (sigma.obj x.1)).2 hzero)
  have hEX : ¬ IsZero (E.functor.obj X).obj :=
    equivalence_obj_not_isZero E X hX
  have hIdemX : ∀ a : End X.obj, a ≫ a = a →
      a = 0 ∨ a = 𝟙 X.obj :=
    projectiveStable_idempotent_eq_zero_or_id
      (sigma.obj x.1) (sigma.indecomposable x.1)
        (sigma.finiteLength x.1)
  have hIdemEX : ∀ a : End (E.functor.obj X).obj, a ≫ a = a →
      a = 0 ∨ a = 𝟙 (E.functor.obj X).obj :=
    equivalence_target_idempotent_eq_zero_or_id E X hIdemX
  exact Classical.choice
    (injectiveStableRepresentative_nonempty sigma
      (E.functor.obj X) hEX hIdemEX)

omit [Finite iota] in
/-- The chosen source representative of `E⁻¹` on one noninjective
cotorsionless skeleton label. -/
noncomputable def backwardStableRepresentative
    (E : TorsionlessStableCategory (R := R) ≌
      CotorsionlessStableCategory (R := R))
    (y : CotorsionlessNoninjectiveLabels sigma) :
    ProjectiveStableRepresentative sigma
      (E.inverse.obj (cotorsionlessStableLabelObject sigma y)) := by
  let Y := cotorsionlessStableLabelObject sigma y
  have hY : ¬ IsZero Y.obj := by
    intro hzero
    exact y.property.2
      ((injective_iff_isZero_injectiveStable (sigma.obj y.1)).2 hzero)
  have hEY : ¬ IsZero (E.inverse.obj Y).obj :=
    equivalence_obj_not_isZero E.symm Y hY
  have hIdemY : ∀ a : End Y.obj, a ≫ a = a →
      a = 0 ∨ a = 𝟙 Y.obj :=
    injectiveStable_idempotent_eq_zero_or_id
      (sigma.obj y.1) (sigma.indecomposable y.1)
        (sigma.finiteLength y.1)
  have hIdemEY : ∀ a : End (E.inverse.obj Y).obj, a ≫ a = a →
      a = 0 ∨ a = 𝟙 (E.inverse.obj Y).obj :=
    equivalence_target_idempotent_eq_zero_or_id E.symm Y hIdemY
  exact Classical.choice
    (projectiveStableRepresentative_nonempty sigma
      (E.inverse.obj Y) hEY hIdemEY)

omit [Finite iota] in
/-- The label selected from the target representative. -/
noncomputable def forwardStableLabel
    (E : TorsionlessStableCategory (R := R) ≌
      CotorsionlessStableCategory (R := R))
    (x : TorsionlessNonprojectiveLabels sigma) :
    CotorsionlessNoninjectiveLabels sigma := by
  let r := forwardStableRepresentative sigma E x
  exact ⟨r.label, r.mem_core, r.noninjective⟩

omit [Finite iota] in
/-- The label selected from the source representative. -/
noncomputable def backwardStableLabel
    (E : TorsionlessStableCategory (R := R) ≌
      CotorsionlessStableCategory (R := R))
    (y : CotorsionlessNoninjectiveLabels sigma) :
    TorsionlessNonprojectiveLabels sigma := by
  let r := backwardStableRepresentative sigma E y
  exact ⟨r.label, r.mem_core, r.nonprojective⟩

omit [Finite iota] in
set_option backward.isDefEq.respectTransparency false in
/-- Any ambient equivalence `L/P ≃ K/Q` gives the exact object-level
stable assignment required by the faithful-core counting theorem. -/
noncomputable def etaStableDataOfAmbientEquivalence
    (E : TorsionlessStableCategory (R := R) ≌
      CotorsionlessStableCategory (R := R)) :
    RingelEtaStableData sigma where
  forward := forwardStableLabel sigma E
  backward := backwardStableLabel sigma E
  source_inverse_stable := by
    intro x
    let fx := forwardStableRepresentative sigma E x
    let y := forwardStableLabel sigma E x
    let bx := backwardStableRepresentative sigma E y
    let z := backwardStableLabel sigma E y
    let X := torsionlessStableLabelObject sigma x
    let Y := cotorsionlessStableLabelObject sigma y
    let Z := torsionlessStableLabelObject sigma z
    let ef : Y ≅ E.functor.obj X :=
      ObjectProperty.isoMk _ fx.iso
    let eb : Z ≅ E.inverse.obj Y :=
      ObjectProperty.isoMk _ bx.iso
    let ezx : Z ≅ X :=
      eb ≪≫ E.inverse.mapIso ef ≪≫ (E.unitIso.app X).symm
    exact stableIsoOfQuotientIso
      ((torsionlessStableProperty (R := R)).ι.mapIso ezx)
  target_inverse_stable := by
    intro y
    let byRep := backwardStableRepresentative sigma E y
    let x := backwardStableLabel sigma E y
    let fy := forwardStableRepresentative sigma E x
    let z := forwardStableLabel sigma E x
    let Y := cotorsionlessStableLabelObject sigma y
    let X := torsionlessStableLabelObject sigma x
    let Z := cotorsionlessStableLabelObject sigma z
    let eb : X ≅ E.inverse.obj Y :=
      ObjectProperty.isoMk _ byRep.iso
    let ef : Z ≅ E.functor.obj X :=
      ObjectProperty.isoMk _ fy.iso
    let ezy : Z ≅ Y :=
      ef ≪≫ E.functor.mapIso eb ≪≫ E.counitIso.app Y
    exact injectiveStableIsoOfQuotientIso
      ((cotorsionlessStableProperty (R := R)).ι.mapIso ezy)

/-- Ringel's compiled ambient `Dη` equivalence supplies faithful-core
cardinality. -/
theorem ringelCoreCardinality_of_ringelEtaStableEquivalence
    [IsNoetherianRing Rᵐᵒᵖ]
    (K : Type u) [Field K] [Algebra K R] [FiniteDimensional K R] :
    RingelCoreCardinality sigma :=
  ringelCoreCardinality_of_etaStableData sigma K
    (etaStableDataOfAmbientEquivalence sigma
      (QuotientSubmoduleEquidistribution.RingelEta.ringelEtaStableEquivalence
        (R := R) K))

end FaithfulCoreAdapter

end QuotientSubmoduleEquidistribution.RingelStable
