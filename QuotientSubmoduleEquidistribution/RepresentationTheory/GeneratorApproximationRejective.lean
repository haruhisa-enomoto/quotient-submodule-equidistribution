import QuotientSubmoduleEquidistribution.CategoryTheory.MonicApproximationRejective
import QuotientSubmoduleEquidistribution.RepresentationTheory.GenericAdditiveRejective

/-!
An objectwise version of the standard additive-generator argument:
a monic right approximation of a finite additive generator propagates
to every object in its finite additive closure.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.CategoricalRejective

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C]

/-- The finite additive closure of an object is itself an additive,
retract-closed subcategory. -/
def finiteAddClosureSubcategory (G : C) :
    CategoricalAdditiveSubcategory.Subcategory C where
  carrier := AuslanderEquivalence.finiteAddClosure G
  biproduct_mem J F hF := by
    classical
    let Q :
        ∀ j : J,
          AuslanderEquivalence.FiniteAddPresentation
            G (F j) :=
      fun j => (hF j).some
    let E : J → C :=
      fun j => ⨁ fun _ : Fin (Q j).n => G
    let sumRetract : Retract (biproduct F) (biproduct E) :=
      { i := biproduct.map fun j => (Q j).retract.i
        r := biproduct.map fun j => (Q j).retract.r
        retract := by
          apply biproduct.hom_ext'
          intro j
          rw [← Category.assoc, biproduct.ι_map,
            Category.assoc, biproduct.ι_map,
            ← Category.assoc,
            (Q j).retract.retract,
            Category.id_comp, Category.comp_id] }
    let flatten :
        biproduct E ≅
          ⨁ fun p : Σ j : J, Fin (Q j).n => G :=
      biproductBiproductIso
        (fun j : J => Fin (Q j).n)
        (fun _ _ => G)
    letI :
        Fintype (Σ j : J, Fin (Q j).n) :=
      Fintype.ofFinite _
    let ε :
        (Σ j : J, Fin (Q j).n) ≃
          Fin (Fintype.card (Σ j : J, Fin (Q j).n)) :=
      Fintype.equivFin _
    let reindex :
        (⨁ fun _ : Σ j : J, Fin (Q j).n => G) ≅
          ⨁ fun _ :
            Fin (Fintype.card
              (Σ j : J, Fin (Q j).n)) => G :=
      biproduct.whiskerEquiv ε
        (fun _ => Iso.refl G)
    exact
      ⟨{
        n := Fintype.card
          (Σ j : J, Fin (Q j).n)
        retract :=
          sumRetract.trans
            ((Retract.ofIso flatten).trans
              (Retract.ofIso reindex)) }⟩
  retract_mem {X Y} r hY := by
    exact
      ⟨{
        n := hY.some.n
        retract := r.trans hY.some.retract }⟩

/-- Finite additive closure is transitive: if `G ∈ add(H)` and
`X ∈ add(G)`, then `X ∈ add(H)`. -/
theorem finiteAddClosure_trans
    {G H X : C}
    (hGH : AuslanderEquivalence.finiteAddClosure H G)
    (hXG : AuslanderEquivalence.finiteAddClosure G X) :
    AuslanderEquivalence.finiteAddClosure H X := by
  let P := finiteAddClosureSubcategory H
  let Q := hXG.some
  apply P.retract_mem Q.retract
  exact
    P.biproduct_mem
      (FintypeCat.of (Fin Q.n))
      (fun _ : Fin Q.n => G)
      (fun _ => hGH)

private def powerApproximation
    (P : CategoricalAdditiveSubcategory.Subcategory C)
    {G : C} (A : MonicRightApproximation P.carrier G)
    (n : ℕ) :
    MonicRightApproximation P.carrier
      (⨁ fun _ : Fin n => G) := by
  let E : Fin n → C := fun _ => A.obj.obj
  let F : Fin n → C := fun _ => G
  let aBase : A.obj.obj ⟶ G := A.map
  have haBase : Mono aBase := by
    dsimp only [aBase]
    exact A.mono
  let S : P.FullSubcategory :=
    ⟨biproduct E,
      P.biproduct_mem (FintypeCat.of (Fin n)) E
        (fun _ => A.obj.property)⟩
  let a : S.obj ⟶ biproduct F :=
    biproduct.map (fun _ : Fin n => aBase)
  have ha : Mono a := by
    constructor
    intro Z f g hfg
    apply biproduct.hom_ext
    intro j
    letI : Mono aBase := haBase
    apply (cancel_mono aBase).1
    calc
      (f ≫ biproduct.π E j) ≫ aBase =
          (f ≫ a) ≫ biproduct.π F j := by
            simp only [a, Category.assoc,
              biproduct.map_π]
      _ = (g ≫ a) ≫ biproduct.π F j := by
        rw [hfg]
      _ = (g ≫ biproduct.π E j) ≫ aBase := by
        simp only [a, Category.assoc,
          biproduct.map_π]
  refine
    { obj := S
      map := a
      mono := ha
      factors := ?_ }
  intro Y f
  choose g hg using
    fun j : Fin n =>
      A.factors Y (f ≫ biproduct.π F j)
  let gBase :
      ∀ j : Fin n, Y.obj ⟶ A.obj.obj :=
    fun j => P.carrier.ι.map (g j)
  have hg0 :
      ∀ j : Fin n,
        gBase j ≫ aBase =
          f ≫ biproduct.π F j := by
    intro j
    dsimp only [gBase, aBase]
    exact hg j
  refine
    ⟨ObjectProperty.homMk
      (biproduct.lift gBase),
      ?_⟩
  have hfactor :
      biproduct.lift gBase ≫
          a =
        f := by
    dsimp only [a]
    rw [biproduct.lift_map]
    apply biproduct.hom_ext
    intro j
    rw [biproduct.lift_π]
    exact hg0 j
  exact hfactor

/-- A monic approximation of `G` by an additive, retract-closed
subcategory propagates to every object in `add(G)`. -/
theorem monicRightApproximation_of_finiteAddPresentation
    (P : CategoricalAdditiveSubcategory.Subcategory C)
    {G X : C}
    [IsIdempotentComplete C]
    (A : MonicRightApproximation P.carrier G)
    (T : AuslanderEquivalence.FiniteAddPresentation G X) :
    Nonempty (MonicRightApproximation P.carrier X) := by
  let An := powerApproximation P A T.n
  let a0 :
      An.obj.obj ⟶
        (⨁ fun _ : Fin T.n => G) :=
    An.map
  have ha0 : Mono a0 := by
    dsimp only [a0]
    exact An.mono
  let p :
      (⨁ fun _ : Fin T.n => G) ⟶
        (⨁ fun _ : Fin T.n => G) :=
    T.retract.r ≫ T.retract.i
  have hp : p ≫ p = p := by
    calc
      p ≫ p =
          T.retract.r ≫
            (T.retract.i ≫ T.retract.r) ≫
              T.retract.i := by
                simp only [p, Category.assoc]
      _ = T.retract.r ≫ 𝟙 X ≫
            T.retract.i := by
              rw [T.retract.retract]
      _ = p := by simp only [p, Category.id_comp]
  obtain ⟨q, hq⟩ :=
    An.factors An.obj (An.map ≫ p)
  have hq0 :
      q.hom ≫ a0 = a0 ≫ p := by
    dsimp only [a0]
    exact hq
  have hq0_idem : q.hom ≫ q.hom = q.hom := by
    letI : Mono a0 := ha0
    apply (cancel_mono a0).1
    calc
      (q.hom ≫ q.hom) ≫ a0 =
          q.hom ≫ (q.hom ≫ a0) :=
        Category.assoc _ _ _
      _ = q.hom ≫ (a0 ≫ p) :=
        congrArg (fun t => q.hom ≫ t) hq0
      _ = (q.hom ≫ a0) ≫ p :=
        (Category.assoc _ _ _).symm
      _ = (a0 ≫ p) ≫ p :=
        congrArg (fun t => t ≫ p) hq0
      _ = a0 ≫ (p ≫ p) := Category.assoc _ _ _
      _ = a0 ≫ p := congrArg (fun t => a0 ≫ t) hp
      _ = q.hom ≫ a0 := hq0.symm
  rcases IsIdempotentComplete.idempotents_split
      An.obj.obj q.hom hq0_idem with
    ⟨Y, inc, proj, hinc_proj, hproj_inc⟩
  have hY : P.carrier Y :=
    P.retract_mem
      { i := inc
        r := proj
        retract := hinc_proj }
      An.obj.property
  let PY : P.FullSubcategory := ⟨Y, hY⟩
  let c : Y ⟶ X :=
    inc ≫ a0 ≫ T.retract.r
  have hinc_q : inc ≫ q.hom = inc := by
    rw [← hproj_inc, ← Category.assoc,
      hinc_proj, Category.id_comp]
  have hc_i :
      c ≫ T.retract.i = inc ≫ a0 := by
    dsimp only [c]
    calc
      (inc ≫ a0 ≫ T.retract.r) ≫
          T.retract.i =
        inc ≫ (a0 ≫ p) := by
          simp only [p, Category.assoc]
      _ = inc ≫ (q.hom ≫ a0) :=
        congrArg (fun t => inc ≫ t) hq0.symm
      _ = (inc ≫ q.hom) ≫ a0 :=
        (Category.assoc _ _ _).symm
      _ = inc ≫ a0 :=
        congrArg (fun t => t ≫ a0) hinc_q
  have hc_mono : Mono c := by
    haveI hinc_mono : Mono inc := by
      constructor
      intro W x y hxy
      calc
        x = x ≫ 𝟙 Y := (Category.comp_id _).symm
        _ = x ≫ (inc ≫ proj) := by rw [hinc_proj]
        _ = (x ≫ inc) ≫ proj :=
          (Category.assoc _ _ _).symm
        _ = (y ≫ inc) ≫ proj := by rw [hxy]
        _ = y ≫ (inc ≫ proj) :=
          Category.assoc _ _ _
        _ = y ≫ 𝟙 Y := by rw [hinc_proj]
        _ = y := Category.comp_id _
    letI ha_mono : Mono a0 := ha0
    constructor
    intro Z f g hfg
    apply (cancel_mono (inc ≫ a0)).1
    calc
      f ≫ (inc ≫ a0) =
          f ≫ (c ≫ T.retract.i) := by rw [hc_i]
      _ = (f ≫ c) ≫ T.retract.i :=
        (Category.assoc _ _ _).symm
      _ = (g ≫ c) ≫ T.retract.i := by rw [hfg]
      _ = g ≫ (c ≫ T.retract.i) :=
        Category.assoc _ _ _
      _ = g ≫ (inc ≫ a0) := by rw [hc_i]
  refine ⟨
    { obj := PY
      map := c
      mono := hc_mono
      factors := ?_ }⟩
  intro Q f
  obtain ⟨g, hg⟩ :=
    An.factors Q (f ≫ T.retract.i)
  have hg0 :
      g.hom ≫ a0 = f ≫ T.retract.i := by
    dsimp only [a0]
    exact hg
  have hgq0 : g.hom ≫ q.hom = g.hom := by
    letI : Mono a0 := ha0
    apply (cancel_mono a0).1
    have hleft :
        (g.hom ≫ q.hom) ≫ a0 =
          f ≫ T.retract.i := by
      calc
        (g.hom ≫ q.hom) ≫ a0 =
            g.hom ≫ (q.hom ≫ a0) :=
          Category.assoc _ _ _
        _ = g.hom ≫ (a0 ≫ p) :=
          congrArg (fun t => g.hom ≫ t) hq0
        _ = (g.hom ≫ a0) ≫ p :=
          (Category.assoc _ _ _).symm
        _ = (f ≫ T.retract.i) ≫ p :=
          congrArg (fun t => t ≫ p) hg0
        _ = f ≫
            (T.retract.i ≫ T.retract.r) ≫
              T.retract.i := by
                simp only [p, Category.assoc]
        _ = f ≫ 𝟙 X ≫ T.retract.i := by
          rw [T.retract.retract]
        _ = f ≫ T.retract.i := by
          simp only [Category.id_comp]
    exact hleft.trans hg0.symm
  let k : Q ⟶ PY :=
    ObjectProperty.homMk
      (P.carrier.ι.map g ≫ proj)
  refine ⟨k, ?_⟩
  simp only [ObjectProperty.ι_map]
  dsimp only [k, c]
  calc
    (g.hom ≫ proj) ≫
          (inc ≫ a0 ≫ T.retract.r) =
        (g.hom ≫ (proj ≫ inc)) ≫
          a0 ≫ T.retract.r := by
            simp only [Category.assoc]
    _ = (g.hom ≫ q.hom) ≫
          a0 ≫ T.retract.r := by rw [hproj_inc]
    _ = ((g.hom ≫ q.hom) ≫ a0) ≫
          T.retract.r :=
      (Category.assoc _ _ _).symm
    _ = (g.hom ≫ a0) ≫
          T.retract.r :=
      congrArg (fun t => (t ≫ a0) ≫
        T.retract.r) hgq0
    _ = (f ≫ T.retract.i) ≫
          T.retract.r :=
      congrArg (fun t => t ≫ T.retract.r) hg0
    _ = f ≫ (T.retract.i ≫
          T.retract.r) :=
      Category.assoc _ _ _
    _ = f ≫ 𝟙 X := by rw [T.retract.retract]
    _ = f := Category.comp_id _

/-- A monic right approximation of a finite additive generator is enough
to make the approximating additive subcategory right rejective. -/
theorem isRightRejective_of_generator_monicRightApproximation
    (P : CategoricalAdditiveSubcategory.Subcategory C)
    {G : C}
    [IsIdempotentComplete C]
    (hG : AuslanderEquivalence.IsFiniteAddGenerator G)
    (A : MonicRightApproximation P.carrier G) :
    IsRightRejective P.carrier :=
  isRightRejective_of_monicRightApproximations
    P.carrier
    (fun X =>
      monicRightApproximation_of_finiteAddPresentation
        P A (hG X).some)

end QuotientSubmoduleEquidistribution.CategoricalRejective
