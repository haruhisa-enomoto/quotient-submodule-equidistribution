import Mathlib.Algebra.Category.ModuleCat.Simple
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import OpConjecture.RepresentationTheory.MaximalFlagStrongHeredity
import OpConjecture.RepresentationTheory.LeftMaximalFlagStrongHeredity

/-!
# Standard-module semantics for strong quasi-heredity

This file records the genuine standard-module side of Tsukamoto's convention
(source `main.tex`, Definition `left`, lines 365--382) and a precise interface
for the CPS comparison with maximal idempotent-ideal chains (Proposition
`lem1`, lines 550--570).
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace OpConjecture.Tsukamoto.StandardSemantics

universe v u w

variable {C : Type u} [Category.{v} C] [Abelian C]
  {ι : Type w} [LinearOrder ι]

/-- A finite filtration whose successive factors belong to the selected
family.  The extension constructor encodes
`0 ⟶ layer i ⟶ X ⟶ Q ⟶ 0`, followed by a filtration of `Q`. -/
inductive IsFilteredBy
    (layer : ι → C) (allowed : ι → Prop) : C → Prop
  | zero (X : C) (hX : IsZero X) :
      IsFilteredBy layer allowed X
  | extension (i : ι) (hi : allowed i)
      {X Q : C} (f : layer i ⟶ X) (g : X ⟶ Q)
      (zero : f ≫ g = 0)
      (exact : (ShortComplex.mk f g zero).ShortExact)
      (tail : IsFilteredBy layer allowed Q) :
      IsFilteredBy layer allowed X

/-- An epimorphism is essential when an arrow into its source is epic as
soon as its composite with the epimorphism is epic. -/
def IsEssentialEpi {X Y : C} (f : X ⟶ Y) : Prop :=
  Epi f ∧
    ∀ ⦃Z : C⦄ (g : Z ⟶ X), Epi (g ≫ f) → Epi g

/-- A categorical projective cover. -/
structure ProjectiveCover (S : C) where
  object : C
  projective : Projective object
  map : object ⟶ S
  essentialEpi : IsEssentialEpi map

namespace ProjectiveCover

/-- Postcomposing a projective cover with an isomorphism of targets gives a
projective cover of the new target. -/
def postIso {S T : C} (P : ProjectiveCover S) (e : S ≅ T) :
    ProjectiveCover T where
  object := P.object
  projective := P.projective
  map := P.map ≫ e.hom
  essentialEpi := by
    letI : Epi P.map := P.essentialEpi.1
    constructor
    · infer_instance
    · intro Z g hg
      haveI : Epi ((g ≫ P.map) ≫ e.hom) := by
        simpa only [Category.assoc] using hg
      haveI : Epi (g ≫ P.map) :=
        (epi_comp_iff_of_isIso (g ≫ P.map) e.hom).mp inferInstance
      exact P.essentialEpi.2 g inferInstance

/-- The sources of any two projective covers of the same object are
isomorphic. -/
def objectIso {S : C} (P Q : ProjectiveCover S) :
    P.object ≅ Q.object := by
  letI : Projective P.object := P.projective
  letI : Projective Q.object := Q.projective
  letI : Epi P.map := P.essentialEpi.1
  letI : Epi Q.map := Q.essentialEpi.1
  let f : P.object ⟶ Q.object :=
    Projective.factorThru P.map Q.map
  have hf : f ≫ Q.map = P.map :=
    Projective.factorThru_comp P.map Q.map
  haveI : Epi (f ≫ Q.map) := hf ▸ inferInstance
  letI : Epi f := Q.essentialEpi.2 f inferInstance
  let r : Q.object ⟶ P.object :=
    Projective.factorThru (𝟙 Q.object) f
  have hr : r ≫ f = 𝟙 Q.object :=
    Projective.factorThru_comp (𝟙 Q.object) f
  have hrf : r ≫ P.map = Q.map := by
    rw [← hf, ← Category.assoc, hr, Category.id_comp]
  haveI : Epi (r ≫ P.map) := hrf ▸ inferInstance
  letI : Epi r := P.essentialEpi.2 r inferInstance
  let split : SplitEpi f := { section_ := r, id := hr }
  letI : IsIso f := IsIso.of_epi_section' split
  exact asIso f

/-- Projective covers of isomorphic objects have isomorphic sources. -/
def objectIsoOfTargetIso {S T : C}
    (P : ProjectiveCover S) (Q : ProjectiveCover T) (e : S ≅ T) :
    P.object ≅ Q.object :=
  objectIso (postIso P e) Q

end ProjectiveCover

/-- The standard module attached to `i`: the maximal quotient of the
projective cover of `S i` all of whose composition factors are indexed by
`j ≤ i`.  "Composition factors" are expressed without multiplicities by
an actual finite simple filtration. -/
structure StandardModule
    (simple : ι → C) (cover : ∀ i, ProjectiveCover (simple i))
    (i : ι) where
  object : C
  projection : (cover i).object ⟶ object
  epi_projection : Epi projection
  simpleFiltered :
    IsFilteredBy simple (fun j ↦ j ≤ i) object
  maximal :
    ∀ ⦃Q : C⦄ (q : (cover i).object ⟶ Q),
      Epi q →
      IsFilteredBy simple (fun j ↦ j ≤ i) Q →
      ∃ u : object ⟶ Q, projection ≫ u = q

/-- The exact standard-module data in the highest-weight part of
Tsukamoto's definition.  The kernel filtration simultaneously expresses
conditions (a) and (b): only standards with strictly larger labels occur.
-/
structure OrderedHighestWeightStructure (C : Type u)
    [Category.{v} C] [Abelian C] (ι : Type w) [LinearOrder ι] where
  simple : ι → C
  simple_isSimple : ∀ i, Simple (simple i)
  simple_complete :
    ∀ (S : C), Simple S →
      ∃ i, Nonempty (S ≅ simple i)
  simple_nodup :
    ∀ {i j}, Nonempty (simple i ≅ simple j) → i = j
  cover : ∀ i, ProjectiveCover (simple i)
  standard : ∀ i, StandardModule simple cover i
  kernel : ι → C
  kernelι : ∀ i, kernel i ⟶ (cover i).object
  kernel_zero :
    ∀ i, kernelι i ≫ (standard i).projection = 0
  kernel_shortExact :
    ∀ i,
      (ShortComplex.mk (kernelι i) (standard i).projection
        (kernel_zero i)).ShortExact
  kernel_standardFiltered :
    ∀ i,
      IsFilteredBy
        (fun j ↦ (standard j).object)
        (fun j ↦ i < j) (kernel i)

namespace OrderedHighestWeightStructure

/-- In the defining projective presentation of a standard module,
projectivity of `K(i)` is equivalent to projective dimension at most one
for `Δ(i)`. -/
theorem kernel_projective_iff_standard_hasProjectiveDimensionLE_one
    (W : OrderedHighestWeightStructure C ι) (i : ι) :
    Projective (W.kernel i) ↔
      HasProjectiveDimensionLE ((W.standard i).object) 1 := by
  rw [projective_iff_hasProjectiveDimensionLT_one]
  exact
    ((W.kernel_shortExact i).hasProjectiveDimensionLT_X₃_iff
      0 (W.cover i).projective).symm

end OrderedHighestWeightStructure

/-- Tsukamoto's right-strong condition: in addition to the ordered
highest-weight structure, every standard-kernel `K(i)` is projective.
This is Definition `left`(1)(c), rather than an ideal-chain synonym. -/
structure RightStronglyQuasiHereditaryStructure (C : Type u)
    [Category.{v} C] [Abelian C] (ι : Type w) [LinearOrder ι]
    extends OrderedHighestWeightStructure C ι where
  kernel_projective : ∀ i, Projective (toOrderedHighestWeightStructure.kernel i)

/-- A left-strong structure on `A` is, literally, a right-strong
standard-module structure on left `A`-modules, i.e. right
`Aᵐᵒᵖ`-modules. -/
abbrev RightStronglyQuasiHereditaryAlgebra
    (A : Type u) [Ring A] (ι : Type w) [LinearOrder ι] :=
  RightStronglyQuasiHereditaryStructure
    (ModuleCat.{max u w} Aᵐᵒᵖ) ι

abbrev LeftStronglyQuasiHereditaryAlgebra
    (A : Type u) [Ring A] (ι : Type w) [LinearOrder ι] :=
  RightStronglyQuasiHereditaryStructure
    (ModuleCat.{max u w} A) ι

/-! ## Exact interface with a maximal ideal chain

The next structure is the missing CPS comparison isolated in the form used
in Tsukamoto's proof of Proposition `lem1`: the ideal layer
`Hᵢ/Hᵢ₊₁` is a positive finite sum of copies of the corresponding standard
module.
-/

universe uA

variable {A : Type uA} [Ring A] {n : ℕ}

/-- The right `A`-module carried by a two-sided ideal. -/
abbrev rightIdealModule (H : TwoSidedIdeal A) :
    ModuleCat.{uA} Aᵐᵒᵖ :=
  ModuleCat.of Aᵐᵒᵖ H

/-- The left `A`-module carried by a two-sided ideal. -/
abbrev leftIdealModule (H : TwoSidedIdeal A) :
    ModuleCat.{uA} A :=
  ModuleCat.of A H

/-- Canonical inclusion of nested two-sided ideals as right modules. -/
def rightIdealInclusion {I J : TwoSidedIdeal A} (h : I ≤ J) :
    rightIdealModule I ⟶ rightIdealModule J :=
  ModuleCat.ofHom
    { toFun := fun x ↦ ⟨x.1, h x.2⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }

/-- Canonical inclusion of nested two-sided ideals as left modules. -/
def leftIdealInclusion {I J : TwoSidedIdeal A} (h : I ≤ J) :
    leftIdealModule I ⟶ leftIdealModule J :=
  ModuleCat.ofHom
    { toFun := fun x ↦ ⟨x.1, h x.2⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }

/-- The canonical right-module inclusion at one step of an ideal chain. -/
def rightChainInclusion (H : IdempotentIdealChain A n) (i : Fin n) :
    rightIdealModule (H.ideal i.succ) ⟶
      rightIdealModule (H.ideal i.castSucc) :=
  rightIdealInclusion
    ((H.strictAnti (Fin.castSucc_lt_succ :
      i.castSucc < i.succ)).le)

/-- The canonical left-module inclusion at one step of an ideal chain. -/
def leftChainInclusion (H : IdempotentIdealChain A n) (i : Fin n) :
    leftIdealModule (H.ideal i.succ) ⟶
      leftIdealModule (H.ideal i.castSucc) :=
  leftIdealInclusion
    ((H.strictAnti (Fin.castSucc_lt_succ :
      i.castSucc < i.succ)).le)

instance rightChainInclusion_mono
    (H : IdempotentIdealChain A n) (i : Fin n) :
    Mono (rightChainInclusion H i) := by
  rw [ModuleCat.mono_iff_injective]
  intro x y hxy
  apply Subtype.ext
  exact
    congrArg
      (fun z : H.ideal i.castSucc ↦ z.1) hxy

instance leftChainInclusion_mono
    (H : IdempotentIdealChain A n) (i : Fin n) :
    Mono (leftChainInclusion H i) := by
  rw [ModuleCat.mono_iff_injective]
  intro x y hxy
  apply Subtype.ext
  exact
    congrArg
      (fun z : H.ideal i.castSucc ↦ z.1) hxy

/-- The literal right-module ideal layer `Hᵢ/Hᵢ₊₁`. -/
abbrev rightIdealLayer (H : IdempotentIdealChain A n) (i : Fin n) :
    ModuleCat.{uA} Aᵐᵒᵖ :=
  cokernel (rightChainInclusion H i)

/-- The literal left-module ideal layer `Hᵢ/Hᵢ₊₁`. -/
abbrev leftIdealLayer (H : IdempotentIdealChain A n) (i : Fin n) :
    ModuleCat.{uA} A :=
  cokernel (leftChainInclusion H i)

theorem rightIdealLayer_shortExact
    (H : IdempotentIdealChain A n) (i : Fin n) :
    (ShortComplex.mk
      (rightChainInclusion H i)
      (cokernel.π (rightChainInclusion H i))
      (cokernel.condition (rightChainInclusion H i))).ShortExact :=
  { exact := ShortComplex.exact_cokernel _ }

theorem leftIdealLayer_shortExact
    (H : IdempotentIdealChain A n) (i : Fin n) :
    (ShortComplex.mk
      (leftChainInclusion H i)
      (cokernel.π (leftChainInclusion H i))
      (cokernel.condition (leftChainInclusion H i))).ShortExact :=
  { exact := ShortComplex.exact_cokernel _ }

/-- Standard-module/CPS data aligned with a maximal idempotent ideal chain
on the right.  It records the exact comparison
`Hᵢ/Hᵢ₊₁ ≅ Δ(i)^{mᵢ}`, with `mᵢ > 0`, used in Tsukamoto's proof. -/
structure RightStandardModuleChainData
    (H : IdempotentIdealChain A n) where
  highestWeight :
    OrderedHighestWeightStructure
      (ModuleCat.{uA} Aᵐᵒᵖ) (Fin n)
  multiplicity : Fin n → ℕ
  multiplicity_pos :
    ∀ i : Fin n, 0 < multiplicity i
  layer_iso_standard_biproduct :
    ∀ i : Fin n,
      rightIdealLayer H i ≅
        ⨁ fun _ : Fin (multiplicity i) ↦
          (highestWeight.standard i).object

/-- The left-module version of `RightStandardModuleChainData`. -/
structure LeftStandardModuleChainData
    (H : IdempotentIdealChain A n) where
  highestWeight :
    OrderedHighestWeightStructure
      (ModuleCat.{uA} A) (Fin n)
  multiplicity : Fin n → ℕ
  multiplicity_pos :
    ∀ i : Fin n, 0 < multiplicity i
  layer_iso_standard_biproduct :
    ∀ i : Fin n,
      leftIdealLayer H i ≅
        ⨁ fun _ : Fin (multiplicity i) ↦
          (highestWeight.standard i).object

namespace RightStandardModuleChainData

/-- A positive standard-module multiplicity makes the standard module a
retract of its ideal layer. -/
def standardRetract
    {H : IdempotentIdealChain A n}
    (D : RightStandardModuleChainData H) (i : Fin n) :
    Retract
      ((D.highestWeight.standard i).object)
      (rightIdealLayer H i) := by
  let F : Fin (D.multiplicity i) → ModuleCat.{uA} Aᵐᵒᵖ :=
    fun _ ↦ (D.highestWeight.standard i).object
  let t : Fin (D.multiplicity i) :=
    ⟨0, D.multiplicity_pos i⟩
  let r :
      Retract ((D.highestWeight.standard i).object) (⨁ F) :=
    { i := biproduct.ι F t
      r := biproduct.π F t
      retract := by simp [F] }
  exact
    r.trans
      (Retract.ofIso
        (D.layer_iso_standard_biproduct i).symm)

end RightStandardModuleChainData

namespace LeftStandardModuleChainData

/-- Left-module version of
`RightStandardModuleChainData.standardRetract`. -/
def standardRetract
    {H : IdempotentIdealChain A n}
    (D : LeftStandardModuleChainData H) (i : Fin n) :
    Retract
      ((D.highestWeight.standard i).object)
      (leftIdealLayer H i) := by
  let F : Fin (D.multiplicity i) → ModuleCat.{uA} A :=
    fun _ ↦ (D.highestWeight.standard i).object
  let t : Fin (D.multiplicity i) :=
    ⟨0, D.multiplicity_pos i⟩
  let r :
      Retract ((D.highestWeight.standard i).object) (⨁ F) :=
    { i := biproduct.ι F t
      r := biproduct.π F t
      retract := by simp [F] }
  exact
    r.trans
      (Retract.ofIso
        (D.layer_iso_standard_biproduct i).symm)

end LeftStandardModuleChainData

private theorem rightIdeal_castSucc_projective
    (H : IdempotentIdealChain A n)
    (hH : H.IsRightStrongHeredity) (i : Fin n) :
    Projective (rightIdealModule (H.ideal i.castSucc)) := by
  letI : Module.Projective Aᵐᵒᵖ (H.ideal i.castSucc) :=
    hH.1 i
  infer_instance

private theorem rightIdeal_succ_projective
    (H : IdempotentIdealChain A n)
    (hH : H.IsRightStrongHeredity) (i : Fin n) :
    Projective (rightIdealModule (H.ideal i.succ)) := by
  by_cases hi : i.val + 1 < n
  · let j : Fin n := ⟨i.val + 1, hi⟩
    have hj : j.castSucc = i.succ := Fin.ext rfl
    letI : Module.Projective Aᵐᵒᵖ (H.ideal i.succ) := by
      rw [← hj]
      exact hH.1 j
    infer_instance
  · have hiv : i.val + 1 = n :=
      le_antisymm (Nat.succ_le_iff.mpr i.isLt)
        (Nat.le_of_not_gt hi)
    have hilast : i.succ = Fin.last n := Fin.ext hiv
    have hzero :
        IsZero (rightIdealModule (H.ideal i.succ)) := by
      rw [hilast, H.bot_eq]
      apply ModuleCat.isZero_iff_subsingleton.mpr
      constructor
      intro x y
      apply Subtype.ext
      rw [(TwoSidedIdeal.mem_bot A).mp x.property,
        (TwoSidedIdeal.mem_bot A).mp y.property]
    exact hzero.projective

private theorem leftIdeal_castSucc_projective
    (H : IdempotentIdealChain A n)
    (hH : H.IsLeftStrongHeredity) (i : Fin n) :
    Projective (leftIdealModule (H.ideal i.castSucc)) := by
  letI : Module.Projective A (H.ideal i.castSucc) :=
    hH.1 i
  infer_instance

private theorem leftIdeal_succ_projective
    (H : IdempotentIdealChain A n)
    (hH : H.IsLeftStrongHeredity) (i : Fin n) :
    Projective (leftIdealModule (H.ideal i.succ)) := by
  by_cases hi : i.val + 1 < n
  · let j : Fin n := ⟨i.val + 1, hi⟩
    have hj : j.castSucc = i.succ := Fin.ext rfl
    letI : Module.Projective A (H.ideal i.succ) := by
      rw [← hj]
      exact hH.1 j
    infer_instance
  · have hiv : i.val + 1 = n :=
      le_antisymm (Nat.succ_le_iff.mpr i.isLt)
        (Nat.le_of_not_gt hi)
    have hilast : i.succ = Fin.last n := Fin.ext hiv
    have hzero :
        IsZero (leftIdealModule (H.ideal i.succ)) := by
      rw [hilast, H.bot_eq]
      apply ModuleCat.isZero_iff_subsingleton.mpr
      constructor
      intro x y
      apply Subtype.ext
      rw [(TwoSidedIdeal.mem_bot A).mp x.property,
        (TwoSidedIdeal.mem_bot A).mp y.property]
    exact hzero.projective

/-- Tsukamoto Proposition `lem1`, rightward implication, after exposing
the exact CPS standard-layer comparison.  The proof follows source lines
561--568: the short exact ideal layer has projective dimension at most one;
the standard module is a retract of that layer; its projective-cover
kernel is therefore projective. -/
def rightStronglyQuasiHereditary_of_chain
    (H : IdempotentIdealChain A n)
    (D : RightStandardModuleChainData H)
    (hH : H.IsRightStrongHeredity) :
    RightStronglyQuasiHereditaryAlgebra A (Fin n) where
  toOrderedHighestWeightStructure := D.highestWeight
  kernel_projective i := by
    letI :
        Projective (rightIdealModule (H.ideal i.castSucc)) :=
      rightIdeal_castSucc_projective H hH i
    letI :
        Projective (rightIdealModule (H.ideal i.succ)) :=
      rightIdeal_succ_projective H hH i
    have hlayer :
        HasProjectiveDimensionLT (rightIdealLayer H i) 2 :=
      ((rightIdealLayer_shortExact H i).hasProjectiveDimensionLT_X₃_iff
        0 (by infer_instance)).mpr (by infer_instance)
    letI : HasProjectiveDimensionLT (rightIdealLayer H i) 2 :=
      hlayer
    have hstandard :
        HasProjectiveDimensionLT
          ((D.highestWeight.standard i).object) 2 :=
      (D.standardRetract i).hasProjectiveDimensionLT 2
    have hkernel :
        HasProjectiveDimensionLT
          (D.highestWeight.kernel i) 1 :=
      ((D.highestWeight.kernel_shortExact i).hasProjectiveDimensionLT_X₃_iff
          0 (D.highestWeight.cover i).projective).mp
        hstandard
    exact projective_iff_hasProjectiveDimensionLT_one.mpr hkernel

/-- The left-module companion of
`rightStronglyQuasiHereditary_of_chain`. -/
def leftStronglyQuasiHereditary_of_chain
    (H : IdempotentIdealChain A n)
    (D : LeftStandardModuleChainData H)
    (hH : H.IsLeftStrongHeredity) :
    LeftStronglyQuasiHereditaryAlgebra A (Fin n) where
  toOrderedHighestWeightStructure := D.highestWeight
  kernel_projective i := by
    letI :
        Projective (leftIdealModule (H.ideal i.castSucc)) :=
      leftIdeal_castSucc_projective H hH i
    letI :
        Projective (leftIdealModule (H.ideal i.succ)) :=
      leftIdeal_succ_projective H hH i
    have hlayer :
        HasProjectiveDimensionLT (leftIdealLayer H i) 2 :=
      ((leftIdealLayer_shortExact H i).hasProjectiveDimensionLT_X₃_iff
        0 (by infer_instance)).mpr (by infer_instance)
    letI : HasProjectiveDimensionLT (leftIdealLayer H i) 2 :=
      hlayer
    have hstandard :
        HasProjectiveDimensionLT
          ((D.highestWeight.standard i).object) 2 :=
      (D.standardRetract i).hasProjectiveDimensionLT 2
    have hkernel :
        HasProjectiveDimensionLT
          (D.highestWeight.kernel i) 1 :=
      ((D.highestWeight.kernel_shortExact i).hasProjectiveDimensionLT_X₃_iff
          0 (D.highestWeight.cover i).projective).mp
        hstandard
    exact projective_iff_hasProjectiveDimensionLT_one.mpr hkernel

/-! ## Application to the compiled maximal-flag chains

These wrappers make the remaining obligation completely explicit: the
strong-heredity proof is now discharged by the compiled flag theorems, while
`D` is precisely the not-yet-formalized CPS standard-module comparison.
-/

universe uR uκ wR uK

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {κ : Type uκ}
  (σ : OpConjecture.IndecomposableSkeleton.{uR, uκ, wR} R κ)
  [Fintype κ]
  {K : Type uK} [Field K] [Algebra K R]
  [∀ i : κ, Module K (σ.obj i)]
  [∀ i : κ, IsScalarTower K R (σ.obj i)]
  [∀ i : κ, FiniteDimensional K (σ.obj i)]

open OpConjecture.IndecomposableSkeleton

/-- A maximal quotient-closed flag gives the conventional right-strong
standard-module structure as soon as its coordinate ideal chain is supplied
with the exact CPS standard-layer data. -/
def rightStronglyQuasiHereditary_of_closedFlag
    (s : OpConjecture.SetClosure.ClosedFlag σ.qClosure)
    (D :
      RightStandardModuleChainData
        (LegalQuotientDeletionChain.flagIdealChain
          (K := K) σ s)) :
    RightStronglyQuasiHereditaryAlgebra
      (OpConjecture.AuslanderEquivalence.CoordinateIdempotent.skeletonAuslanderAlgebra σ)
      (Fin (Fintype.card κ)) :=
  rightStronglyQuasiHereditary_of_chain
    (LegalQuotientDeletionChain.flagIdealChain
      (K := K) σ s)
    D
    (LegalQuotientDeletionChain.flagIdealChain_isRightStrongHeredity
      (K := K) σ s)

/-- A maximal subobject-closed flag gives the conventional left-strong
standard-module structure under the corresponding CPS standard-layer
comparison. -/
def leftStronglyQuasiHereditary_of_closedFlag
    (hfinite :
      ∀ X : FGModuleCat.{wR} R, IsFiniteLength R X)
    (s : OpConjecture.SetClosure.ClosedFlag σ.sClosure)
    (D :
      LeftStandardModuleChainData
        (LegalSubobjectDeletionChain.leftFlagIdealChain
          (K := K) σ s)) :
    LeftStronglyQuasiHereditaryAlgebra
      (OpConjecture.AuslanderEquivalence.CoordinateIdempotent.skeletonAuslanderAlgebra σ)
      (Fin (Fintype.card κ)) :=
  leftStronglyQuasiHereditary_of_chain
    (LegalSubobjectDeletionChain.leftFlagIdealChain
      (K := K) σ s)
    D
    (LegalSubobjectDeletionChain.leftFlagIdealChain_isLeftStrongHeredity
      (K := K) σ hfinite s)

end OpConjecture.Tsukamoto.StandardSemantics
