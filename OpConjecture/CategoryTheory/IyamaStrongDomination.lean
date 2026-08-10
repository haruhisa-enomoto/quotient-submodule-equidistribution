import OpConjecture.CategoryTheory.IyamaLeftLadderIteration
import OpConjecture.CategoryTheory.IyamaKrullSchmidtDirectFinite
import OpConjecture.CategoryTheory.IyamaLadderComparisonAssembly

/-!
# Split-monic domination of arrows

This scratch file isolates Iyama's relation `a l≫ b`: the arrow `b` maps
to the arrow `a` by a commuting square whose source and target maps are split
monomorphisms.  It records the preorder calculus and the two literal
zero-padding witnesses used by the constructed right and left ladders.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace OpConjecture.Iyama

universe v u w

variable {C : Type u} [Category.{v} C]

/-- Iyama's strong left domination `a l≫ b`: `b` is a split-monic
sub-square of `a`. -/
def LeftStrongDomination
    {Xa Ya Xb Yb : C} (a : Xa ⟶ Ya) (b : Xb ⟶ Yb) : Prop :=
  ∃ d : Arrow.mk b ⟶ Arrow.mk a,
    IsSplitMono d.left ∧ IsSplitMono d.right

namespace LeftStrongDomination

/-- An explicit split-monic arrow square gives strong left domination. -/
theorem of_hom
    {Xa Ya Xb Yb : C} {a : Xa ⟶ Ya} {b : Xb ⟶ Yb}
    (d : Arrow.mk b ⟶ Arrow.mk a)
    (hleft : IsSplitMono d.left) (hright : IsSplitMono d.right) :
    LeftStrongDomination a b :=
  ⟨d, hleft, hright⟩

/-- Strong left domination is reflexive. -/
theorem refl {X Y : C} (a : X ⟶ Y) : LeftStrongDomination a a := by
  refine ⟨𝟙 (Arrow.mk a), ?_, ?_⟩ <;> infer_instance

/-- Strong left domination is transitive. -/
theorem trans
    {Xa Ya Xb Yb Xc Yc : C}
    {a : Xa ⟶ Ya} {b : Xb ⟶ Yb} {c : Xc ⟶ Yc}
    (hab : LeftStrongDomination a b)
    (hbc : LeftStrongDomination b c) :
    LeftStrongDomination a c := by
  obtain ⟨d, hdleft, hdright⟩ := hab
  obtain ⟨e, heleft, heright⟩ := hbc
  haveI : IsSplitMono d.left := hdleft
  haveI : IsSplitMono d.right := hdright
  letI : IsSplitMono e.left := heleft
  letI : IsSplitMono e.right := heright
  refine ⟨e ≫ d, ?_, ?_⟩
  · change IsSplitMono (e.left ≫ d.left)
    infer_instance
  · change IsSplitMono (e.right ≫ d.right)
    infer_instance

/-- An arrow isomorphism gives domination in its forward orientation. -/
theorem of_iso
    {Xa Ya Xb Yb : C} {a : Xa ⟶ Ya} {b : Xb ⟶ Yb}
    (e : Arrow.mk b ≅ Arrow.mk a) : LeftStrongDomination a b := by
  refine ⟨e.hom, ?_, ?_⟩ <;> infer_instance

/-- An arrow isomorphism gives domination in both orientations. -/
theorem both_of_iso
    {Xa Ya Xb Yb : C} {a : Xa ⟶ Ya} {b : Xb ⟶ Yb}
    (e : Arrow.mk a ≅ Arrow.mk b) :
    LeftStrongDomination a b ∧ LeftStrongDomination b a :=
  ⟨of_iso e.symm, of_iso e⟩

/-- An object is directly finite when each split-monic endomorphism is
invertible. -/
def IsDirectlyFiniteObject (X : C) : Prop :=
  ∀ e : X ⟶ X, IsSplitMono e → IsIso e

/-- The exact category-level finiteness property needed to turn mutual
split-monic domination into an arrow isomorphism. -/
def HasDirectlyFiniteEndomorphisms : Prop :=
  ∀ X : C, IsDirectlyFiniteObject X

/-- Dedekind finiteness of every endomorphism monoid supplies the categorical
direct-finiteness interface. -/
theorem hasDirectlyFiniteEndomorphisms_of_isDedekindFiniteMonoid
    (hfinite : ∀ X : C, IsDedekindFiniteMonoid (End X)) :
    HasDirectlyFiniteEndomorphisms (C := C) := by
  intro X e he
  letI : IsSplitMono e := he
  letI : IsDedekindFiniteMonoid (End X) := hfinite X
  let q : End X := End.of e
  let r : End X := End.of (retraction e)
  have her : e ≫ retraction e = 𝟙 X := IsSplitMono.id e
  have hre : retraction e ≫ e = 𝟙 X := by
    have hmul : r * q = 1 := by
      apply End.ext
      simpa only [q, r, End.mul_def, End.one_def, End.of] using her
    have hmul' : q * r = 1 := mul_eq_one_symm hmul
    have hhom := congrArg (fun z : End X ↦ End.asHom z) hmul'
    simpa only [q, r, End.mul_def, End.one_def, End.of,
      End.asHom] using hhom
  exact ⟨⟨retraction e, her, hre⟩⟩

/-- Local form of domination antisymmetry: direct finiteness is needed only
for the source and target of the receiving arrow `a`. -/
theorem nonempty_arrow_iso_of_mutual_of_directlyFinite_targets
    {Xa Ya Xb Yb : C} {a : Xa ⟶ Ya} {b : Xb ⟶ Yb}
    (hXa : IsDirectlyFiniteObject Xa)
    (hYa : IsDirectlyFiniteObject Ya)
    (hab : LeftStrongDomination a b)
    (hba : LeftStrongDomination b a) :
    Nonempty (Arrow.mk a ≅ Arrow.mk b) := by
  obtain ⟨d, hdleft, hdright⟩ := hab
  obtain ⟨e, heleft, heright⟩ := hba
  letI : IsSplitMono d.left := hdleft
  letI : IsSplitMono d.right := hdright
  letI : IsSplitMono e.left := heleft
  letI : IsSplitMono e.right := heright
  have hleftCompSplit : IsSplitMono (e.left ≫ d.left) := inferInstance
  have hrightCompSplit : IsSplitMono (e.right ≫ d.right) := inferInstance
  haveI hleftCompIso : IsIso (e.left ≫ d.left) :=
    hXa _ hleftCompSplit
  haveI hrightCompIso : IsIso (e.right ≫ d.right) :=
    hYa _ hrightCompSplit
  have hdleftEpi : IsSplitEpi d.left := by
    apply IsSplitEpi.mk'
    exact
      { section_ := inv (e.left ≫ d.left) ≫ e.left
        id := by
          rw [Category.assoc, IsIso.inv_hom_id] }
  have hdrightEpi : IsSplitEpi d.right := by
    apply IsSplitEpi.mk'
    exact
      { section_ := inv (e.right ≫ d.right) ≫ e.right
        id := by
          rw [Category.assoc, IsIso.inv_hom_id] }
  letI : IsSplitEpi d.left := hdleftEpi
  letI : IsSplitEpi d.right := hdrightEpi
  have hdleftIso : IsIso d.left :=
    isIso_of_mono_of_isSplitEpi d.left
  have hdrightIso : IsIso d.right :=
    isIso_of_mono_of_isSplitEpi d.right
  letI : IsIso d.left := hdleftIso
  letI : IsIso d.right := hdrightIso
  have hdIso : IsIso d :=
    Arrow.isIso_of_isIso_left_of_isIso_right d
  letI : IsIso d := hdIso
  exact ⟨(asIso d).symm⟩

/-- In a category with directly finite endomorphisms, mutual strong left
domination is antisymmetric up to isomorphism in the arrow category. -/
theorem nonempty_arrow_iso_of_mutual
    (hfinite : HasDirectlyFiniteEndomorphisms (C := C))
    {Xa Ya Xb Yb : C} {a : Xa ⟶ Ya} {b : Xb ⟶ Yb}
    (hab : LeftStrongDomination a b)
    (hba : LeftStrongDomination b a) :
    Nonempty (Arrow.mk a ≅ Arrow.mk b) :=
  nonempty_arrow_iso_of_mutual_of_directlyFinite_targets
    (hfinite Xa) (hfinite Ya) hab hba

/-- Four domination steps which close to a cycle make all adjacent arrows
isomorphic.  This is the literal shape of the terminal diagonal in Iyama's
finite comparison. -/
theorem nonempty_adjacent_arrow_isos_of_four_cycle
    (hfinite : HasDirectlyFiniteEndomorphisms (C := C))
    {X₀ Y₀ X₁ Y₁ X₂ Y₂ X₃ Y₃ : C}
    {a₀ : X₀ ⟶ Y₀} {a₁ : X₁ ⟶ Y₁}
    {a₂ : X₂ ⟶ Y₂} {a₃ : X₃ ⟶ Y₃}
    (h₀₁ : LeftStrongDomination a₀ a₁)
    (h₁₂ : LeftStrongDomination a₁ a₂)
    (h₂₃ : LeftStrongDomination a₂ a₃)
    (h₃₀ : LeftStrongDomination a₃ a₀) :
    Nonempty (Arrow.mk a₀ ≅ Arrow.mk a₁) ∧
      Nonempty (Arrow.mk a₁ ≅ Arrow.mk a₂) ∧
      Nonempty (Arrow.mk a₂ ≅ Arrow.mk a₃) ∧
      Nonempty (Arrow.mk a₃ ≅ Arrow.mk a₀) := by
  refine ⟨nonempty_arrow_iso_of_mutual hfinite h₀₁ ?_,
    nonempty_arrow_iso_of_mutual hfinite h₁₂ ?_,
    nonempty_arrow_iso_of_mutual hfinite h₂₃ ?_,
    nonempty_arrow_iso_of_mutual hfinite h₃₀ ?_⟩
  · exact h₁₂.trans (h₂₃.trans h₃₀)
  · exact h₂₃.trans (h₃₀.trans h₀₁)
  · exact h₃₀.trans (h₀₁.trans h₁₂)
  · exact h₀₁.trans (h₁₂.trans h₂₃)

/-- A single domination square is already an arrow isomorphism when both
receiving endpoint objects are indecomposable and both embedded endpoint
objects are nonzero. -/
theorem nonempty_arrow_iso_of_indecomposable_targets
    [Preadditive C] [HasBinaryBiproducts C] [IsIdempotentComplete C]
    {Xa Ya Xb Yb : C} {a : Xa ⟶ Ya} {b : Xb ⟶ Yb}
    (hXa : Indecomposable Xa) (hYa : Indecomposable Ya)
    (hXb : ¬ IsZero Xb) (hYb : ¬ IsZero Yb)
    (hab : LeftStrongDomination a b) :
    Nonempty (Arrow.mk a ≅ Arrow.mk b) := by
  obtain ⟨d, hdleft, hdright⟩ := hab
  haveI hdleftSplit : IsSplitMono d.left := hdleft
  haveI hdrightSplit : IsSplitMono d.right := hdright
  have hdleftIso : IsIso d.left :=
    @LeftLadder.Comparison.isIso_of_isSplitMono_to_indecomposable
      C _ _ _ _ Xb Xa hXa d.left hdleft hXb
  have hdrightIso : IsIso d.right :=
    @LeftLadder.Comparison.isIso_of_isSplitMono_to_indecomposable
      C _ _ _ _ Yb Ya hYa d.right hdright hYb
  letI : IsIso d.left := hdleftIso
  letI : IsIso d.right := hdrightIso
  have hdIso : IsIso d :=
    Arrow.isIso_of_isIso_left_of_isIso_right d
  letI : IsIso d := hdIso
  exact ⟨(asIso d).symm⟩

end LeftStrongDomination

variable [Preadditive C] [HasBinaryBiproducts C]

/-- A zero-padded source row strongly left-dominates its essential
component. -/
theorem leftStrongDomination_biprod_desc_zero
    {Z U Y : C} (b : Z ⟶ Y) :
    LeftStrongDomination
      (biprod.desc b (0 : U ⟶ Y)) b := by
  let d : Arrow.mk b ⟶
      Arrow.mk (biprod.desc b (0 : U ⟶ Y)) :=
    { left := biprod.inl
      right := 𝟙 Y
      w := by
        change biprod.inl ≫ biprod.desc b 0 = b ≫ 𝟙 Y
        rw [biprod.inl_desc, Category.comp_id] }
  refine ⟨d, ?_, ?_⟩
  · change IsSplitMono (biprod.inl : Z ⟶ Z ⊞ U)
    infer_instance
  · change IsSplitMono (𝟙 Y)
    infer_instance

/-- A zero-padded target column strongly left-dominates its essential
component. -/
theorem leftStrongDomination_biprod_lift_zero
    {X Z U : C} (b : X ⟶ Z) :
    LeftStrongDomination
      (biprod.lift b (0 : X ⟶ U)) b := by
  let d : Arrow.mk b ⟶
      Arrow.mk (biprod.lift b (0 : X ⟶ U)) :=
    { left := 𝟙 X
      right := biprod.inl
      w := by
        change 𝟙 X ≫ biprod.lift b 0 = b ≫ biprod.inl
        rw [Category.id_comp]
        apply biprod.hom_ext <;> simp }
  refine ⟨d, ?_, ?_⟩
  · change IsSplitMono (𝟙 X)
    infer_instance
  · change IsSplitMono (biprod.inl : Z ⟶ Z ⊞ U)
    infer_instance

variable [HasFiniteBiproducts C] [IsIdempotentComplete C]
variable {Ind : Type w} [Fintype Ind]
variable {T : FiniteTauCategoryData C Ind}

/-- Finite Krull--Schmidt cancellation makes every endomorphism object
directly finite. -/
theorem FiniteTauCategoryData.hasDirectlyFiniteEndomorphisms
    (T : FiniteTauCategoryData C Ind) :
    LeftStrongDomination.HasDirectlyFiniteEndomorphisms (C := C) := by
  intro X e he
  letI : IsSplitMono e := he
  exact T.isIso_of_isSplitMono_end e

/-- On arrows between chosen indecomposable representatives, one strong
left domination is automatically an arrow isomorphism. -/
theorem FiniteTauCategoryData.nonempty_arrow_iso_of_leftStrongDomination_obj
    (T : FiniteTauCategoryData C Ind)
    {A B A' B' : Ind}
    (a : T.obj A ⟶ T.obj B) (b : T.obj A' ⟶ T.obj B')
    (hab : LeftStrongDomination a b) :
    Nonempty (Arrow.mk a ≅ Arrow.mk b) :=
  LeftStrongDomination.nonempty_arrow_iso_of_indecomposable_targets
    (T.obj_indec A) (T.obj_indec B)
    (T.obj_indec A').1 (T.obj_indec B').1 hab

/-- Every literal arrow in the constructed right ladder strongly
left-dominates its normalized essential factor. -/
theorem RightLadder.Comparison.paddedArrow_leftStrongDominates_essential
    {X₀ Y₀ : C} {a₀ : X₀ ⟶ Y₀}
    (L : RightLadder.InfiniteSpecialRightLadder
      T.toFiniteRightTauCategoryData a₀) (i : ℕ) :
    LeftStrongDomination
      (RightLadder.Comparison.paddedArrow L i) (L.b i) :=
  leftStrongDomination_biprod_desc_zero (L.b i)

/-- Every literal arrow in a finite constructed left ladder strongly
left-dominates its normalized essential factor. -/
theorem LeftLadder.FiniteSpecialLeftLadderFromZero.paddedArrow_leftStrongDominates_essential
    {U₀ : C} {n : ℕ}
    (L : LeftLadder.FiniteSpecialLeftLadderFromZero T U₀ n)
    (i : Fin (n + 1)) :
    LeftStrongDomination (L.paddedArrow i) (L.b i) :=
  leftStrongDomination_biprod_lift_zero (L.b i)

/-- The same target-padding witness for every rung of the infinite
constructed left ladder. -/
theorem LeftLadder.InfiniteSpecialLeftLadderFromZero.paddedArrow_leftStrongDominates_essential
    {U₀ : C}
    (L : LeftLadder.InfiniteSpecialLeftLadderFromZero T U₀)
    (i : ℕ) :
    LeftStrongDomination
      (biprod.lift (L.b i) (0 : L.Y i ⟶ L.U i)) (L.b i) :=
  leftStrongDomination_biprod_lift_zero (L.b i)

end OpConjecture.Iyama
