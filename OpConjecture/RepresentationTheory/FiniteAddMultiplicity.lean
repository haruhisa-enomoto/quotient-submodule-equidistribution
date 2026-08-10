import OpConjecture.RepresentationTheory.AuslanderEquivalence
import OpConjecture.RepresentationTheory.EndomorphismRadical
import OpConjecture.RepresentationTheory.FiniteLengthDecomposition

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace OpConjecture.FiniteAddMultiplicity

universe u w

variable {R : Type u} [Ring R] [IsNoetherianRing R]

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

omit [IsNoetherianRing R] in
/-- An indecomposable summand of a finite power of an indecomposable
finite-length module is isomorphic to that module. -/
theorem indecomposable_retract_of_power_iso
    (X Z : FGModuleCat.{w} R)
    (hXindec : OpConjecture.Foundation.IsIndecomposableModule R X)
    (hZfinite : IsFiniteLength R Z)
    (hZindec : OpConjecture.Foundation.IsIndecomposableModule R Z)
    {n : ℕ}
    (P : Retract Z (⨁ fun _ : Fin n ↦ X)) :
    Nonempty (Z ≅ X) := by
  let comp : Fin n → Module.End R Z :=
    fun i ↦
      (biproduct.ι (fun _ : Fin n ↦ X) i ≫ P.r).hom.hom.comp
        (P.i ≫ biproduct.π (fun _ : Fin n ↦ X) i).hom.hom
  have hcat :
      ∑ i : Fin n,
          (P.i ≫ biproduct.π (fun _ : Fin n ↦ X) i) ≫
            (biproduct.ι (fun _ : Fin n ↦ X) i ≫ P.r) =
        𝟙 Z := by
    calc
      _ =
          P.i ≫
            (∑ i : Fin n,
              biproduct.π (fun _ : Fin n ↦ X) i ≫
                biproduct.ι (fun _ : Fin n ↦ X) i) ≫
            P.r := by
          simp only [Category.assoc, Preadditive.comp_sum,
            Preadditive.sum_comp]
      _ = P.i ≫ P.r := by rw [biproduct.total]; simp
      _ = 𝟙 Z := P.retract
  let underlying :
      (Z ⟶ Z) →+ Module.End R Z :=
    { toFun := fun f ↦ f.hom.hom
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  have hsum :
      (∑ i : Fin n,
          ((P.i ≫ biproduct.π (fun _ : Fin n ↦ X) i) ≫
            (biproduct.ι (fun _ : Fin n ↦ X) i ≫ P.r)).hom.hom) =
        ∑ i : Fin n, comp i := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [comp, FGModuleCat.hom_hom_comp]
  have hcompSum : (∑ i : Fin n, comp i) = 1 := by
    calc
      _ =
          ∑ i : Fin n,
            underlying
              ((P.i ≫ biproduct.π (fun _ : Fin n ↦ X) i) ≫
                (biproduct.ι (fun _ : Fin n ↦ X) i ≫ P.r)) := hsum.symm
      _ =
          underlying
            (∑ i : Fin n,
              (P.i ≫ biproduct.π (fun _ : Fin n ↦ X) i) ≫
                (biproduct.ι (fun _ : Fin n ↦ X) i ≫ P.r)) := by
            symm
            exact map_sum underlying _ Finset.univ
      _ = underlying (𝟙 Z) := congrArg underlying hcat
      _ = 1 := rfl
  letI : IsLocalRing (Module.End R Z) :=
    OpConjecture.Foundation.isLocalRing_end_of_isIndecomposable hZfinite hZindec
  have hunit : IsUnit (∑ i : Fin n, comp i) := by
    rw [hcompSum]
    exact isUnit_one
  obtain ⟨i, _, hiunit⟩ :=
    IsLocalRing.exists_of_isUnit_sum
      (s := Finset.univ) (f := comp) hunit
  obtain ⟨e⟩ :=
    OpConjecture.nonempty_linearEquiv_of_isUnit_comp
      hZindec hXindec
      (biproduct.ι (fun _ : Fin n ↦ X) i ≫ P.r).hom.hom
      (P.i ≫ biproduct.π (fun _ : Fin n ↦ X) i).hom.hom
      hiunit
  exact ⟨e.toFGModuleCatIso⟩

/-- The finite additive closure of one indecomposable finite-length
module contains no new indecomposable isomorphism types. -/
theorem finiteAddClosure_is_biproduct
    (X Y : FGModuleCat.{w} R)
    (hXindec : OpConjecture.Foundation.IsIndecomposableModule R X)
    (hYfinite : IsFiniteLength R Y)
    (hYadd : AuslanderEquivalence.finiteAddClosure X Y) :
    ∃ m : ℕ, Nonempty (Y ≅ ⨁ fun _ : Fin m ↦ X) := by
  obtain ⟨m, Z, hZindec, ⟨eY⟩⟩ :=
    FiniteLengthDecomposition.exists_fin_biproduct_decomposition
      Y hYfinite
  obtain ⟨P⟩ := hYadd
  let summandRetract (j : Fin m) :
      Retract (Z j) (⨁ fun _ : Fin P.n ↦ X) :=
    { i :=
        biproduct.ι Z j ≫ eY.inv ≫ P.retract.i
      r :=
        P.retract.r ≫ eY.hom ≫ biproduct.π Z j
      retract := by
        simp [Category.assoc] }
  have summandι_injective (j : Fin m) :
      Function.Injective
        (biproduct.ι Z j ≫ eY.inv).hom.hom := by
    refine Function.LeftInverse.injective
      (g := (eY.hom ≫ biproduct.π Z j).hom.hom) ?_
    intro z
    have hcat :
        (biproduct.ι Z j ≫ eY.inv) ≫
            (eY.hom ≫ biproduct.π Z j) =
          𝟙 (Z j) := by
      simp [Category.assoc]
    exact ConcreteCategory.congr_hom hcat z
  let summandIso (j : Fin m) : Z j ≅ X :=
    (indecomposable_retract_of_power_iso
      X (Z j) hXindec
      (hYfinite.of_injective
        (f :=
          (biproduct.ι Z j ≫ eY.inv).hom.hom)
        (summandι_injective j))
      (hZindec j) (summandRetract j)).some
  exact ⟨m, ⟨eY ≪≫ biproduct.mapIso summandIso⟩⟩

end OpConjecture.FiniteAddMultiplicity
