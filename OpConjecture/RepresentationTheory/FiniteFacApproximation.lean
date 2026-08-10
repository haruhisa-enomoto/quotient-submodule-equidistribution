import OpConjecture.RepresentationTheory.Approximation
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.LinearAlgebra.StdBasis

/-!
# Covariant approximations for finitely generated quotient classes

Over a finite-dimensional algebra, this file constructs left approximations
for every `Fac(add B)` with finite indecomposable support `B`.  It is the
finite-cover input needed to complete the Auslander--Smalø approximation
theorem without a project-local axiom.
-/

noncomputable section

open Set
open CategoryTheory CategoryTheory.Limits

namespace OpConjecture.IndecomposableSkeleton

universe uK uR uP v w

variable {K : Type uK} [Field K]
  {R : Type uR} [Ring R] [Algebra K R] [FiniteDimensional K R]
  [IsNoetherianRing R]

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- Scalar multiplication of the identity, regarded as an `R`-linear
endomorphism. -/
private noncomputable def scalarId
    (M : FGModuleCat.{w} R)
    [Module K M] [IsScalarTower K R M]
    (c : K) : M ⟶ M :=
  ConcreteCategory.ofHom (c • LinearMap.id)

/-- The evaluation map associated to a finite basis of `Hom_R(P,M)`. -/
private noncomputable def homEvaluation
    (P M : FGModuleCat.{uR} R)
    [Module K P] [IsScalarTower K R P] [FiniteDimensional K P]
    [Module K M] [IsScalarTower K R M] [FiniteDimensional K M] :
    let d := Module.finrank K (P →ₗ[R] M)
    P ⟶ (⨁ fun _ : FintypeCat.of (Fin d) ↦ M) :=
  biproduct.lift fun i ↦
    ConcreteCategory.ofHom
      (Module.finBasis K (P →ₗ[R] M) i)

omit [FiniteDimensional K R] [IsNoetherianRing R] in
/-- Finite-dimensional evaluation is universal for maps from `P` to `M`. -/
private theorem homEvaluation_factors
    (P M : FGModuleCat.{uR} R)
    [Module K P] [IsScalarTower K R P] [FiniteDimensional K P]
    [Module K M] [IsScalarTower K R M] [FiniteDimensional K M]
    (h : P ⟶ M) :
    let d := Module.finrank K (P →ₗ[R] M)
    let E := (⨁ fun _ : FintypeCat.of (Fin d) ↦ M)
    ∃ l : E ⟶ M, homEvaluation (K := K) P M ≫ l = h := by
  classical
  let b := Module.finBasis K (P →ₗ[R] M)
  let d := Module.finrank K (P →ₗ[R] M)
  let E := (⨁ fun _ : FintypeCat.of (Fin d) ↦ M)
  let l : E ⟶ M :=
    biproduct.desc fun i ↦
      scalarId (K := K) M (b.repr h.hom.hom i)
  refine ⟨l, ?_⟩
  dsimp only [homEvaluation, l]
  rw [biproduct.lift_desc]
  apply FGModuleCat.hom_ext
  let underlying :
      (P ⟶ M) →+ (P →ₗ[R] M) :=
    { toFun := fun f ↦ f.hom.hom
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  have hmodule :
      (∑ i : Fin d,
        ConcreteCategory.ofHom (b i) ≫
          scalarId (K := K) M (b.repr h.hom.hom i)).hom.hom =
        ∑ i : Fin d,
          (ConcreteCategory.ofHom (b i) ≫
            scalarId (K := K) M
              (b.repr h.hom.hom i)).hom.hom := by
    change underlying (∑ i : Fin d,
        ConcreteCategory.ofHom (b i) ≫
          scalarId (K := K) M (b.repr h.hom.hom i)) =
      ∑ i : Fin d, underlying
        (ConcreteCategory.ofHom (b i) ≫
          scalarId (K := K) M (b.repr h.hom.hom i))
    exact map_sum underlying _ Finset.univ
  rw [hmodule]
  simp only [FGModuleCat.hom_hom_comp]
  change
    (∑ i : Fin d,
      ((b.repr h.hom.hom i) • LinearMap.id) ∘ₗ b i =
      h.hom.hom)
  rw [← b.sum_repr h.hom.hom]
  apply Finset.sum_congr rfl
  intro i _
  ext x
  simp

omit [FiniteDimensional K R] [IsNoetherianRing R] in
/-- Evaluation also captures maps into finite biproducts of retracts of
`M`. -/
private theorem homEvaluation_factors_biproduct_of_retracts
    (P M : FGModuleCat.{uR} R)
    [Module K P] [IsScalarTower K R P] [FiniteDimensional K P]
    [Module K M] [IsScalarTower K R M] [FiniteDimensional K M]
    (J : FintypeCat.{0}) (F : J → FGModuleCat.{uR} R)
    (inc : ∀ j, F j ⟶ M) (proj : ∀ j, M ⟶ F j)
    (hsplit : ∀ j, inc j ≫ proj j = 𝟙 (F j))
    (h : P ⟶ biproduct F) :
    let d := Module.finrank K (P →ₗ[R] M)
    let E := (⨁ fun _ : FintypeCat.of (Fin d) ↦ M)
    ∃ l : E ⟶ biproduct F,
      homEvaluation (K := K) P M ≫ l = h := by
  classical
  let d := Module.finrank K (P →ₗ[R] M)
  let E := (⨁ fun _ : FintypeCat.of (Fin d) ↦ M)
  choose l hl using fun j ↦
    homEvaluation_factors (K := K) P M
      (h ≫ biproduct.π F j ≫ inc j)
  let q : E ⟶ biproduct F :=
    biproduct.lift fun j ↦ l j ≫ proj j
  refine ⟨q, ?_⟩
  apply biproduct.hom_ext
  intro j
  simp only [q, Category.assoc, biproduct.lift_π]
  rw [← Category.assoc, hl j, Category.assoc, Category.assoc,
    hsplit j, Category.comp_id]

/-- Every selected summand with label in `range b` is a specified retract
of the sum over `b`. -/
private theorem selectedSummands_retract_supportSum
    {ι : Type v} (σ : IndecomposableSkeleton.{uR, v, w} R ι)
    {n : ℕ} (b : Fin n → ι)
    (J : FintypeCat.{0}) (a : J → ι)
    (ha : ∀ j, a j ∈ Set.range b) :
    ∃ (inc : ∀ j, σ.obj (a j) ⟶ σ.sumOver (FintypeCat.of (Fin n)) b)
      (proj : ∀ j, σ.sumOver (FintypeCat.of (Fin n)) b ⟶ σ.obj (a j)),
      ∀ j, inc j ≫ proj j = 𝟙 (σ.obj (a j)) := by
  classical
  let pick (j : J) : Fin n := Classical.choose (ha j)
  have hpick (j : J) : b (pick j) = a j :=
    Classical.choose_spec (ha j)
  let inc (j : J) :
      σ.obj (a j) ⟶ σ.sumOver (FintypeCat.of (Fin n)) b :=
    eqToHom (congrArg σ.obj (hpick j).symm) ≫
      biproduct.ι (fun t : Fin n ↦ σ.obj (b t)) (pick j)
  let proj (j : J) :
      σ.sumOver (FintypeCat.of (Fin n)) b ⟶ σ.obj (a j) :=
    biproduct.π (fun t : Fin n ↦ σ.obj (b t)) (pick j) ≫
      eqToHom (congrArg σ.obj (hpick j))
  refine ⟨inc, proj, ?_⟩
  intro j
  simp [inc, proj, Category.assoc]

/-- Abstract projective-presentation bridge.  An evaluation map out of a
projective cover descends to a left approximation after quotienting its
target by the image of the presentation kernel. -/
private theorem leftApproximation_of_projectiveEvaluation
    {ι : Type v} (σ : IndecomposableSkeleton.{uR, v, uR} R ι)
    (B : Set ι) (X P E : FGModuleCat.{uR} R)
    [Module.Projective R P]
    (p : P ⟶ X) (hp : Function.Surjective p.hom.hom)
    (e : P ⟶ E) (hE : σ.InFac B E)
    (heval :
      ∀ (J : FintypeCat.{0}) (a : J → ι),
        (∀ j, a j ∈ B) →
        ∀ h : P ⟶ σ.sumOver J a,
          ∃ l : E ⟶ σ.sumOver J a, e ≫ l = h) :
    Nonempty (LeftApproximation (σ.InFac B) X) := by
  classical
  let U : Submodule R E :=
    (LinearMap.ker p.hom.hom).map e.hom.hom
  let Q : FGModuleCat.{uR} R :=
    FGModuleCat.of R (E ⧸ U)
  let q : E ⟶ Q :=
    ConcreteCategory.ofHom U.mkQ
  have hq_surj : Function.Surjective q.hom.hom :=
    Submodule.mkQ_surjective U
  letI : Epi q := (fg_epi_iff_surjective q).2 hq_surj
  have hQ : σ.InFac B Q :=
    inFac_of_epi σ hE q
  have hker_map :
      LinearMap.ker p.hom.hom ≤
        U.comap e.hom.hom := by
    intro x hx
    exact ⟨x, hx, rfl⟩
  let ebar :
      (P ⧸ LinearMap.ker p.hom.hom) →ₗ[R] (E ⧸ U) :=
    (LinearMap.ker p.hom.hom).mapQ U e.hom.hom hker_map
  let pEquiv :
      (P ⧸ LinearMap.ker p.hom.hom) ≃ₗ[R] X :=
    p.hom.hom.quotKerEquivOfSurjective hp
  let alin : X →ₗ[R] (E ⧸ U) :=
    ebar.comp pEquiv.symm.toLinearMap
  let approxMap : X ⟶ Q :=
    ConcreteCategory.ofHom alin
  have hp_approx :
      p ≫ approxMap = e ≫ q := by
    apply FGModuleCat.hom_ext
    ext x
    change alin (p.hom.hom x) = U.mkQ (e.hom.hom x)
    dsimp only [alin]
    rw [LinearMap.comp_apply]
    change ebar (pEquiv.symm (p.hom.hom x)) =
      U.mkQ (e.hom.hom x)
    rw [show pEquiv.symm (p.hom.hom x) =
      Submodule.Quotient.mk x by
        exact p.hom.hom.quotKerEquivOfSurjective_symm_apply hp x]
    rfl
  refine ⟨{
    object := Q
    mem := hQ
    map := approxMap
    factors := ?_ }⟩
  intro Y hY f
  obtain ⟨T⟩ := hY
  have hT_surj : Function.Surjective T.map.hom.hom :=
    (fg_epi_iff_surjective T.map).1 T.epi
  obtain ⟨hlin, hlift⟩ :=
    Module.projective_lifting_property
      T.map.hom.hom (f.hom.hom.comp p.hom.hom) hT_surj
  let h : P ⟶ σ.sumOver T.index T.label :=
    ConcreteCategory.ofHom hlin
  obtain ⟨l, hl⟩ :=
    heval T.index T.label T.mem h
  have hl_linear :
      l.hom.hom.comp e.hom.hom = hlin := by
    calc
      l.hom.hom.comp e.hom.hom = h.hom.hom := by
        exact congrArg (fun z ↦ z.hom.hom) hl
      _ = hlin := rfl
  have hU_ker :
      U ≤ LinearMap.ker (T.map.hom.hom.comp l.hom.hom) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hz
    apply LinearMap.mem_ker.mpr
    have hx0 : p.hom.hom x = 0 :=
      LinearMap.mem_ker.mp hx
    calc
      T.map.hom.hom (l.hom.hom (e.hom.hom x)) =
          T.map.hom.hom (hlin x) := by
            have hxle := LinearMap.congr_fun hl_linear x
            exact congrArg T.map.hom.hom hxle
      _ = f.hom.hom (p.hom.hom x) := by
            exact LinearMap.congr_fun hlift x
      _ = 0 := by rw [hx0, map_zero]
  let rlin : (E ⧸ U) →ₗ[R] Y :=
    U.liftQ (T.map.hom.hom.comp l.hom.hom) hU_ker
  let r : Q ⟶ Y :=
    ConcreteCategory.ofHom rlin
  refine ⟨r, ?_⟩
  letI : Epi p := (fg_epi_iff_surjective p).2 hp
  apply (cancel_epi p).1
  have hq_r : q ≫ r = l ≫ T.map := by
    apply FGModuleCat.hom_ext
    exact U.liftQ_mkQ
      (T.map.hom.hom.comp l.hom.hom) hU_ker
  have hh_T : h ≫ T.map = p ≫ f := by
    apply FGModuleCat.hom_ext
    exact hlift
  rw [← Category.assoc, hp_approx, Category.assoc, hq_r,
    ← Category.assoc, hl, hh_T]

/-- The finite-cover theorem in the same universe as the algebra.  The
finite-dimensional hypotheses make all relevant Hom spaces finite, while a
finite free presentation supplies the projective source. -/
theorem finiteFacCovariantlyFinite_of_finiteDimensional_sameUniverse
    (K : Type uK) [Field K] [Algebra K R] [FiniteDimensional K R]
    {ι : Type v}
    (σ : IndecomposableSkeleton.{uR, v, uR} R ι) :
    FiniteFacCovariantlyFinite σ := by
  classical
  intro B hB X
  obtain ⟨n, b, rfl⟩ := hB.fin_embedding
  obtain ⟨m, plin, hp⟩ :=
    Module.Finite.exists_fin' R X
  let P : FGModuleCat.{uR} R :=
    FGModuleCat.of R (Fin m → R)
  let p : P ⟶ X :=
    ConcreteCategory.ofHom plin
  let M : FGModuleCat.{uR} R :=
    σ.sumOver (FintypeCat.of (Fin n)) b
  letI : FiniteDimensional K P :=
    Module.Finite.trans R P
  letI : Module K M :=
    Module.restrictScalars K R M
  letI : IsScalarTower K R M :=
    IsScalarTower.restrictScalars K R M
  letI : FiniteDimensional K M :=
    Module.Finite.trans R M
  letI : Module.Projective R P :=
    Module.Projective.of_basis (Pi.basisFun R (Fin m))
  let d := Module.finrank K (P →ₗ[R] M)
  let D : FintypeCat.{0} :=
    FintypeCat.of (Fin d)
  let E : FGModuleCat.{uR} R :=
    biproduct fun _ : D ↦ M
  let e : P ⟶ E :=
    homEvaluation (K := K) P M
  have hM : σ.InFac (Set.range b) M := by
    refine ⟨{
      index := FintypeCat.of (Fin n)
      label := b
      mem := fun j ↦ ⟨j, rfl⟩
      map := 𝟙 M
      epi := inferInstance }⟩
  have hE : σ.InFac (Set.range b) E :=
    inFac_biproduct σ D (fun _ ↦ M) fun _ ↦ hM
  have heval :
      ∀ (J : FintypeCat.{0}) (a : J → ι),
        (∀ j, a j ∈ Set.range b) →
        ∀ h : P ⟶ σ.sumOver J a,
          ∃ l : E ⟶ σ.sumOver J a, e ≫ l = h := by
    intro J a ha h
    obtain ⟨inc, proj, hsplit⟩ :=
      selectedSummands_retract_supportSum σ b J a ha
    exact
      homEvaluation_factors_biproduct_of_retracts
        (K := K) P M J (fun j ↦ σ.obj (a j))
        inc proj hsplit h
  exact
    leftApproximation_of_projectiveEvaluation
      σ (Set.range b) X P E p hp e hE heval

/-- Cross-universe form of the Hom-basis evaluation map.  Its source is an
unbundled module, so it need not live in the universe of `FGModuleCat`. -/
private noncomputable def homEvaluationLinear
    (P : Type uP) [AddCommGroup P] [Module R P]
    [Module K P] [IsScalarTower K R P] [FiniteDimensional K P]
    (M : FGModuleCat.{w} R)
    [Module K M] [IsScalarTower K R M] [FiniteDimensional K M] :
    let d := Module.finrank K (P →ₗ[R] M)
    P →ₗ[R]
      ((⨁ fun _ : FintypeCat.of (Fin d) ↦ M) :
        FGModuleCat.{w} R) :=
  ∑ i : Fin (Module.finrank K (P →ₗ[R] M)),
    (biproduct.ι
      (fun _ : Fin (Module.finrank K (P →ₗ[R] M)) ↦ M) i).hom.hom.comp
        (Module.finBasis K (P →ₗ[R] M) i)

omit [FiniteDimensional K R] [IsNoetherianRing R] in
/-- Every map from a possibly differently-sized projective source into `M`
factors linearly through the evaluation map. -/
private theorem homEvaluationLinear_factors
    (P : Type uP) [AddCommGroup P] [Module R P]
    [Module K P] [IsScalarTower K R P] [FiniteDimensional K P]
    (M : FGModuleCat.{w} R)
    [Module K M] [IsScalarTower K R M] [FiniteDimensional K M]
    (h : P →ₗ[R] M) :
    let d := Module.finrank K (P →ₗ[R] M)
    let E := (⨁ fun _ : FintypeCat.of (Fin d) ↦ M)
    ∃ l : E ⟶ M,
      l.hom.hom.comp (homEvaluationLinear (K := K) P M) = h := by
  classical
  let b := Module.finBasis K (P →ₗ[R] M)
  let d := Module.finrank K (P →ₗ[R] M)
  let E := (⨁ fun _ : FintypeCat.of (Fin d) ↦ M)
  let l : E ⟶ M :=
    biproduct.desc fun i ↦
      scalarId (K := K) M (b.repr h i)
  refine ⟨l, ?_⟩
  ext x
  change
    l.hom.hom
      ((∑ i : Fin d,
        (biproduct.ι (fun _ : Fin d ↦ M) i).hom.hom.comp (b i)) x) =
      h x
  rw [LinearMap.sum_apply, map_sum]
  calc
    ∑ i : Fin d,
        l.hom.hom
          (((biproduct.ι (fun _ : Fin d ↦ M) i).hom.hom.comp
            (b i)) x) =
        ∑ i : Fin d, (b.repr h i) • (b i) x := by
          apply Finset.sum_congr rfl
          intro i _
          have hcat :
              biproduct.ι (fun _ : Fin d ↦ M) i ≫ l =
                scalarId (K := K) M (b.repr h i) := by
            exact biproduct.ι_desc _ _
          have hlin := congrArg (fun q ↦ q.hom.hom) hcat
          have happ :=
            LinearMap.congr_fun hlin ((b i) x)
          exact happ.trans (by rfl)
    _ = (∑ i : Fin d, (b.repr h i) • b i) x := by
          rw [LinearMap.sum_apply]
          simp
    _ = h x := by rw [b.sum_repr h]

omit [IsNoetherianRing R] in
/-- Evaluation of a finite sum of morphisms in `FGModuleCat`, stated at
the level of elements. -/
private theorem fg_hom_sum_apply
    {J : Type} [Fintype J]
    {X Y : FGModuleCat.{w} R}
    (f : J → (X ⟶ Y)) (x : X) :
    ((∑ j, f j).hom.hom) x =
      ∑ j, (f j).hom.hom x := by
  let underlying :
      (X ⟶ Y) →+ (X →ₗ[R] Y) :=
    { toFun := fun g ↦ g.hom.hom
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  have h₁ :
      (∑ j, f j).hom.hom =
        ∑ j, (f j).hom.hom := by
    change underlying (∑ j, f j) =
      ∑ j, underlying (f j)
    exact map_sum underlying f Finset.univ
  rw [h₁, LinearMap.sum_apply]

omit [IsNoetherianRing R] in
/-- The projections of a finite biproduct jointly separate underlying
elements. -/
private theorem biproduct_element_ext
    {J : Type} [Fintype J]
    (F : J → FGModuleCat.{w} R)
    (x y : ((biproduct F) : FGModuleCat.{w} R))
    (h : ∀ j,
      (biproduct.π F j).hom.hom x =
        (biproduct.π F j).hom.hom y) :
    x = y := by
  classical
  let term (j : J) :
      biproduct F ⟶ biproduct F :=
    biproduct.π F j ≫ biproduct.ι F j
  have hsum :
      ((∑ j, term j).hom.hom) x =
        ((∑ j, term j).hom.hom) y := by
    rw [fg_hom_sum_apply (f := term) x,
      fg_hom_sum_apply (f := term) y]
    apply Finset.sum_congr rfl
    intro j _
    have hj := congrArg
      (fun z ↦ (biproduct.ι F j).hom.hom z) (h j)
    simpa only [term, FGModuleCat.hom_hom_comp,
      LinearMap.comp_apply] using hj
  have htotal :
      (∑ j, term j) = 𝟙 (biproduct F) := by
    exact biproduct.total
      (C := FGModuleCat.{w} R) (f := F)
  rw [htotal] at hsum
  exact hsum

omit [FiniteDimensional K R] [IsNoetherianRing R] in
/-- Cross-universe evaluation captures maps into finite biproducts of
retracts of `M`. -/
private theorem homEvaluationLinear_factors_biproduct_of_retracts
    (P : Type uP) [AddCommGroup P] [Module R P]
    [Module K P] [IsScalarTower K R P] [FiniteDimensional K P]
    (M : FGModuleCat.{w} R)
    [Module K M] [IsScalarTower K R M] [FiniteDimensional K M]
    (J : FintypeCat.{0}) (F : J → FGModuleCat.{w} R)
    (inc : ∀ j, F j ⟶ M) (proj : ∀ j, M ⟶ F j)
    (hsplit : ∀ j, inc j ≫ proj j = 𝟙 (F j))
    (h : P →ₗ[R] ((biproduct F) : FGModuleCat.{w} R)) :
    let d := Module.finrank K (P →ₗ[R] M)
    let E := (⨁ fun _ : FintypeCat.of (Fin d) ↦ M)
    ∃ l : E ⟶ biproduct F,
      l.hom.hom.comp (homEvaluationLinear (K := K) P M) = h := by
  classical
  letI : Fintype J := FintypeCat.fintype
  let d := Module.finrank K (P →ₗ[R] M)
  let E := (⨁ fun _ : FintypeCat.of (Fin d) ↦ M)
  let componentToM (j : J) : P →ₗ[R] M :=
    inc j |>.hom.hom.comp
      ((biproduct.π F j).hom.hom.comp h)
  choose l hl using fun j ↦
    homEvaluationLinear_factors (K := K) P M
      (componentToM j)
  let q : E ⟶ biproduct F :=
    biproduct.lift fun j ↦ l j ≫ proj j
  refine ⟨q, ?_⟩
  ext x
  apply biproduct_element_ext F
  intro j
  have hqj :
      q ≫ biproduct.π F j = l j ≫ proj j := by
    exact biproduct.lift_π _ _
  have hqj_linear :=
    congrArg (fun z ↦ z.hom.hom) hqj
  have hqj_app :=
    LinearMap.congr_fun hqj_linear
      (homEvaluationLinear (K := K) P M x)
  have hl_app :=
    LinearMap.congr_fun (hl j) x
  have hsplit_linear :=
    congrArg (fun z ↦ z.hom.hom) (hsplit j)
  have hsplit_app :=
    LinearMap.congr_fun hsplit_linear
      ((biproduct.π F j).hom.hom (h x))
  calc
    (biproduct.π F j).hom.hom
        ((q.hom.hom.comp
          (homEvaluationLinear (K := K) P M)) x) =
        (proj j).hom.hom
          ((l j).hom.hom
            (homEvaluationLinear (K := K) P M x)) := hqj_app
    _ = (proj j).hom.hom
          ((inc j).hom.hom
            ((biproduct.π F j).hom.hom (h x))) := by
          exact congrArg (proj j).hom.hom hl_app
    _ = (biproduct.π F j).hom.hom (h x) := hsplit_app

/-- Cross-universe projective-presentation bridge. -/
private theorem leftApproximation_of_projectiveEvaluationLinear
    {ι : Type v} (σ : IndecomposableSkeleton.{uR, v, w} R ι)
    (B : Set ι) (X : FGModuleCat.{w} R)
    (P : Type uP) [AddCommGroup P] [Module R P]
    [Module.Projective R P]
    (p : P →ₗ[R] X) (hp : Function.Surjective p)
    (E : FGModuleCat.{w} R) (e : P →ₗ[R] E)
    (hE : σ.InFac B E)
    (heval :
      ∀ (J : FintypeCat.{0}) (a : J → ι),
        (∀ j, a j ∈ B) →
        ∀ h : P →ₗ[R] σ.sumOver J a,
          ∃ l : E ⟶ σ.sumOver J a,
            l.hom.hom.comp e = h) :
    Nonempty (LeftApproximation (σ.InFac B) X) := by
  classical
  let U : Submodule R E :=
    (LinearMap.ker p).map e
  let Q : FGModuleCat.{w} R :=
    FGModuleCat.of R (E ⧸ U)
  let q : E ⟶ Q :=
    ConcreteCategory.ofHom U.mkQ
  have hq_surj : Function.Surjective q.hom.hom :=
    Submodule.mkQ_surjective U
  letI : Epi q := (fg_epi_iff_surjective q).2 hq_surj
  have hQ : σ.InFac B Q :=
    inFac_of_epi σ hE q
  have hker_map :
      LinearMap.ker p ≤ U.comap e := by
    intro x hx
    exact ⟨x, hx, rfl⟩
  let ebar :
      (P ⧸ LinearMap.ker p) →ₗ[R] (E ⧸ U) :=
    (LinearMap.ker p).mapQ U e hker_map
  let pEquiv :
      (P ⧸ LinearMap.ker p) ≃ₗ[R] X :=
    p.quotKerEquivOfSurjective hp
  let alin : X →ₗ[R] (E ⧸ U) :=
    ebar.comp pEquiv.symm.toLinearMap
  let approxMap : X ⟶ Q :=
    ConcreteCategory.ofHom alin
  have hp_approx (x : P) :
      alin (p x) = U.mkQ (e x) := by
    dsimp only [alin]
    rw [LinearMap.comp_apply]
    change ebar (pEquiv.symm (p x)) =
      U.mkQ (e x)
    rw [show pEquiv.symm (p x) =
      Submodule.Quotient.mk x by
        exact p.quotKerEquivOfSurjective_symm_apply hp x]
    rfl
  refine ⟨{
    object := Q
    mem := hQ
    map := approxMap
    factors := ?_ }⟩
  intro Y hY f
  obtain ⟨T⟩ := hY
  have hT_surj : Function.Surjective T.map.hom.hom :=
    (fg_epi_iff_surjective T.map).1 T.epi
  obtain ⟨hlin, hlift⟩ :=
    Module.projective_lifting_property
      T.map.hom.hom (f.hom.hom.comp p) hT_surj
  obtain ⟨l, hl⟩ :=
    heval T.index T.label T.mem hlin
  have hU_ker :
      U ≤ LinearMap.ker (T.map.hom.hom.comp l.hom.hom) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hz
    apply LinearMap.mem_ker.mpr
    have hx0 : p x = 0 :=
      LinearMap.mem_ker.mp hx
    have hl_app :=
      LinearMap.congr_fun hl x
    calc
      T.map.hom.hom (l.hom.hom (e x)) =
          T.map.hom.hom (hlin x) := by
            exact congrArg T.map.hom.hom hl_app
      _ = f.hom.hom (p x) := by
            exact LinearMap.congr_fun hlift x
      _ = 0 := by rw [hx0, map_zero]
  let rlin : (E ⧸ U) →ₗ[R] Y :=
    U.liftQ (T.map.hom.hom.comp l.hom.hom) hU_ker
  let r : Q ⟶ Y :=
    ConcreteCategory.ofHom rlin
  refine ⟨r, ?_⟩
  apply FGModuleCat.hom_ext
  ext x
  obtain ⟨z, rfl⟩ := hp x
  change rlin (alin (p z)) = f.hom.hom (p z)
  calc
    rlin (alin (p z)) =
        rlin (U.mkQ (e z)) := by rw [hp_approx z]
    _ = T.map.hom.hom (l.hom.hom (e z)) := rfl
    _ = T.map.hom.hom (hlin z) := by
          exact congrArg T.map.hom.hom
            (LinearMap.congr_fun hl z)
    _ = f.hom.hom (p z) := by
          exact LinearMap.congr_fun hlift z

/-- Finite quotient generation is covariantly finite for an arbitrary
`FGModuleCat` universe over a finite-dimensional algebra. -/
theorem finiteFacCovariantlyFinite_of_finiteDimensional
    (K : Type uK) [Field K] [Algebra K R] [FiniteDimensional K R]
    {ι : Type v} (σ : IndecomposableSkeleton.{uR, v, w} R ι) :
    FiniteFacCovariantlyFinite σ := by
  classical
  intro B hB X
  obtain ⟨n, b, rfl⟩ := hB.fin_embedding
  obtain ⟨m, p, hp⟩ :=
    Module.Finite.exists_fin' R X
  let P := Fin m → R
  let M : FGModuleCat.{w} R :=
    σ.sumOver (FintypeCat.of (Fin n)) b
  letI : FiniteDimensional K P :=
    Module.Finite.trans R P
  letI : Module.Projective R P :=
    Module.Projective.of_basis (Pi.basisFun R (Fin m))
  letI : Module K M :=
    Module.restrictScalars K R M
  letI : IsScalarTower K R M :=
    IsScalarTower.restrictScalars K R M
  letI : FiniteDimensional K M :=
    Module.Finite.trans R M
  let d := Module.finrank K (P →ₗ[R] M)
  let D : FintypeCat.{0} :=
    FintypeCat.of (Fin d)
  let E : FGModuleCat.{w} R :=
    biproduct fun _ : D ↦ M
  let e : P →ₗ[R] E :=
    homEvaluationLinear (K := K) P M
  have hM : σ.InFac (Set.range b) M := by
    refine ⟨{
      index := FintypeCat.of (Fin n)
      label := b
      mem := fun j ↦ ⟨j, rfl⟩
      map := 𝟙 M
      epi := inferInstance }⟩
  have hE : σ.InFac (Set.range b) E :=
    inFac_biproduct σ D (fun _ ↦ M) fun _ ↦ hM
  have heval :
      ∀ (J : FintypeCat.{0}) (a : J → ι),
        (∀ j, a j ∈ Set.range b) →
        ∀ h : P →ₗ[R] σ.sumOver J a,
          ∃ l : E ⟶ σ.sumOver J a,
            l.hom.hom.comp e = h := by
    intro J a ha h
    obtain ⟨inc, proj, hsplit⟩ :=
      selectedSummands_retract_supportSum σ b J a ha
    exact
      homEvaluationLinear_factors_biproduct_of_retracts
        (K := K) P M J (fun j ↦ σ.obj (a j))
        inc proj hsplit h
  exact
    leftApproximation_of_projectiveEvaluationLinear
      σ (Set.range b) X P p hp E e hE heval

/-- Over a finite-dimensional algebra, compact quotient-closed supports are
functorially finite, with no remaining approximation hypothesis. -/
theorem inFac_functoriallyFinite_of_isCompactElement_of_finiteDimensional
    (K : Type uK) [Field K] [Algebra K R] [FiniteDimensional K R]
    {ι : Type v} (σ : IndecomposableSkeleton.{uR, v, w} R ι)
    {C : σ.qClosure.Closeds} (hcompact : IsCompactElement C) :
    IsFunctoriallyFinite (σ.InFac (C : Set ι)) :=
  inFac_functoriallyFinite_of_isCompactElement σ
    (finiteFacCovariantlyFinite_of_finiteDimensional K σ) hcompact

/-- Exact compactness-versus-functorial-finiteness theorem over a
finite-dimensional algebra, for any displayed finite generator of the
ambient finitely generated module category. -/
theorem isCompactElement_iff_inFac_functoriallyFinite_of_finiteDimensional
    (K : Type uK) [Field K] [Algebra K R] [FiniteDimensional K R]
    {ι : Type v} (σ : IndecomposableSkeleton.{uR, v, w} R ι)
    (G : FGModuleCat.{w} R) (hG : IsFiniteGenerator G)
    {C : σ.qClosure.Closeds} :
    IsCompactElement C ↔
      IsFunctoriallyFinite (σ.InFac (C : Set ι)) :=
  isCompactElement_iff_inFac_functoriallyFinite σ G hG
    (finiteFacCovariantlyFinite_of_finiteDimensional K σ)

/-- Same-universe form using the regular module as the canonical finite
generator. -/
theorem isCompactElement_iff_inFac_functoriallyFinite_of_finiteDimensional_sameUniverse
    (K : Type uK) [Field K] [Algebra K R] [FiniteDimensional K R]
    {ι : Type v} (σ : IndecomposableSkeleton.{uR, v, uR} R ι)
    {C : σ.qClosure.Closeds} :
    IsCompactElement C ↔
      IsFunctoriallyFinite (σ.InFac (C : Set ι)) :=
  isCompactElement_iff_inFac_functoriallyFinite_of_finiteDimensional
    K σ (FGModuleCat.of R R) (regularObject_isFiniteGenerator R)

end OpConjecture.IndecomposableSkeleton
