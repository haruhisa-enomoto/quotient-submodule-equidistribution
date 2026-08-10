import OpConjecture.CategoryTheory.NilpotentCategoricalRadical
import OpConjecture.RepresentationDirected.IyamaWordMeshAdditiveHull

/-!
# The radical of the abstract word-mesh additive hull

This module identifies the categorical radical with the strictly-forward
matrix ideal and proves that its `Q.length`th power vanishes.  No concrete
algebra, quiver representation, or module classification is used.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace OpConjecture.RepresentationDirected.IyamaMesh.WordMesh.AdditiveHull

universe uK uL

variable {K : Type uK} [Field K]
variable {L : Type uL}

open OpConjecture.RepresentationDirected.ARWord
open OpConjecture.CategoricalIdeal
open OpConjecture.CategoricalRadical

/-- A matrix morphism has gap `n` if each possibly nonzero entry advances
by at least `n` positions in the word. -/
def HasGap (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    {X Y : Category (K := K) G Q hAlt}
    (n : ℕ) (f : X ⟶ Y) : Prop :=
  ∀ i j, ¬ (X.X i).val + n ≤ (Y.X j).val → f i j = 0

/-- Directedness says that every morphism has gap zero. -/
theorem hasGap_zero_of_directed
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    {X Y : Category (K := K) G Q hAlt}
    (f : X ⟶ Y) : HasGap (K := K) G Q hAlt 0 f := by
  intro i j hij
  apply WordMesh.hom_eq_zero_of_not_le G Q hAlt
  intro hle
  exact hij (by simpa using hle)

/-- Gaps add under composition. -/
theorem HasGap.comp
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    {X Y Z : Category (K := K) G Q hAlt}
    {m n : ℕ} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : HasGap (K := K) G Q hAlt m f)
    (hg : HasGap (K := K) G Q hAlt n g) :
    HasGap (K := K) G Q hAlt (m + n) (f ≫ g) := by
  classical
  intro i k hik
  rw [Mat_.comp_apply, Finset.sum_eq_zero]
  intro j _
  by_cases hij : (X.X i).val + m ≤ (Y.X j).val
  · have hjk : ¬ (Y.X j).val + n ≤ (Z.X k).val := by
      omega
    rw [hg j k hjk, comp_zero]
  · rw [hf i j hij, zero_comp]

/-- The zero morphism has every gap. -/
theorem HasGap.zero
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    {X Y : Category (K := K) G Q hAlt} (n : ℕ) :
    HasGap (K := K) G Q hAlt n (0 : X ⟶ Y) := by
  intro i j _
  rfl

/-- Gap conditions are closed under addition. -/
theorem HasGap.add
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    {X Y : Category (K := K) G Q hAlt}
    {n : ℕ} {f g : X ⟶ Y}
    (hf : HasGap (K := K) G Q hAlt n f)
    (hg : HasGap (K := K) G Q hAlt n g) :
    HasGap (K := K) G Q hAlt n (f + g) := by
  intro i j hij
  rw [Mat_.add_apply, hf i j hij, hg i j hij, add_zero]

/-- Gap conditions are closed under negation. -/
theorem HasGap.neg
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    {X Y : Category (K := K) G Q hAlt}
    {n : ℕ} {f : X ⟶ Y}
    (hf : HasGap (K := K) G Q hAlt n f) :
    HasGap (K := K) G Q hAlt n (-f) := by
  intro i j hij
  rw [show (-f) i j = -(f i j) by rfl, hf i j hij, neg_zero]

/-- The strictly-forward matrices form a two-sided additive Hom ideal. -/
def strictForwardIdeal
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) :
    HomIdeal (Category (K := K) G Q hAlt) where
  hom X Y :=
    { carrier := {f | HasGap (K := K) G Q hAlt 1 f}
      zero_mem' := HasGap.zero G Q hAlt 1
      add_mem' := fun hf hg ↦ hf.add G Q hAlt hg
      neg_mem' := fun hf ↦ hf.neg G Q hAlt }
  precomp := by
    intro X Y Z a g hg
    have ha := hasGap_zero_of_directed G Q hAlt a
    simpa using ha.comp G Q hAlt hg
  postcomp := by
    intro X Y Z f b hf
    have hb := hasGap_zero_of_directed G Q hAlt b
    simpa using hf.comp G Q hAlt hb

/-- Strict forwardness is equivalently zero on entries joining equal word
vertices. -/
theorem mem_strictForwardIdeal_iff_equal_entries_zero
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    {X Y : Category (K := K) G Q hAlt}
    (f : X ⟶ Y) :
    f ∈ (strictForwardIdeal (K := K) G Q hAlt).hom X Y ↔
      ∀ i j, X.X i = Y.X j → f i j = 0 := by
  constructor
  · intro hf i j hij
    change HasGap (K := K) G Q hAlt 1 f at hf
    apply hf i j
    rw [hij]
    omega
  · intro hf
    change HasGap (K := K) G Q hAlt 1 f
    intro i j hij
    by_cases heq : X.X i = Y.X j
    · exact hf i j heq
    · apply WordMesh.hom_eq_zero_of_not_le G Q hAlt
      intro hle
      have hneval : (X.X i).val ≠ (Y.X j).val := by
        intro hval
        apply heq
        exact Fin.ext hval
      omega

/-- Membership in the `n`th power forces a positional gap of `n`. -/
theorem hasGap_of_mem_strictForwardIdeal_pow
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) :
    ∀ (n : ℕ) {X Y : Category (K := K) G Q hAlt} {f : X ⟶ Y},
      f ∈ ((strictForwardIdeal (K := K) G Q hAlt).pow n).hom X Y →
        HasGap (K := K) G Q hAlt n f := by
  intro n
  induction n with
  | zero =>
      intro X Y f _
      exact hasGap_zero_of_directed G Q hAlt f
  | succ n ih =>
      intro X Y f hf
      rw [HomIdeal.pow_succ] at hf
      induction hf using AddSubgroup.closure_induction with
      | mem f hf =>
          obtain ⟨M, a, b, ha, hb, rfl⟩ := hf
          change HasGap (K := K) G Q hAlt 1 b at hb
          simpa [Nat.succ_eq_add_one] using
            (ih ha).comp G Q hAlt hb
      | zero => exact HasGap.zero G Q hAlt (n + 1)
      | add f g _ _ hf hg => exact hf.add G Q hAlt hg
      | neg f _ hf => exact hf.neg G Q hAlt

/-- A gap as long as the word forces a matrix morphism to vanish. -/
theorem eq_zero_of_hasGap_length
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    {X Y : Category (K := K) G Q hAlt}
    {f : X ⟶ Y}
    (hf : HasGap (K := K) G Q hAlt Q.length f) :
    f = 0 := by
  apply Mat_.hom_ext
  intro i j
  apply hf i j
  have hj := (Y.X j).isLt
  omega

/-- The strictly-forward ideal is nilpotent, with exponent the word
length. -/
theorem strictForwardIdeal_isNilpotent
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) :
    (strictForwardIdeal (K := K) G Q hAlt).IsNilpotent := by
  refine ⟨Q.length, ?_⟩
  apply HomIdeal.ext_hom
  intro X Y
  apply le_antisymm
  · intro f hf
    change f = 0
    exact eq_zero_of_hasGap_length G Q hAlt
      (hasGap_of_mem_strictForwardIdeal_pow G Q hAlt Q.length hf)
  · exact bot_le

/-- A strictly-forward endomorphism is nilpotent. -/
theorem isNilpotent_end_of_hasGap_one
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    {X : Category (K := K) G Q hAlt}
    (f : X ⟶ X)
    (hf : HasGap (K := K) G Q hAlt 1 f) :
    IsNilpotent (End.of f) := by
  have hpow : ∀ n : ℕ,
      HasGap (K := K) G Q hAlt n ((End.of f) ^ n) := by
    intro n
    induction n with
    | zero =>
        change HasGap (K := K) G Q hAlt 0 (1 : End X)
        exact hasGap_zero_of_directed G Q hAlt _
    | succ n ih =>
        rw [pow_succ, End.mul_def]
        simpa [Nat.succ_eq_add_one, Nat.add_comm] using
          hf.comp G Q hAlt ih
  refine ⟨Q.length, ?_⟩
  exact eq_zero_of_hasGap_length G Q hAlt (hpow Q.length)

/-- Every strictly-forward matrix morphism is categorically radical. -/
theorem isRadicalMorphism_of_mem_strictForwardIdeal
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    {X Y : Category (K := K) G Q hAlt}
    (f : X ⟶ Y)
    (hf : f ∈ (strictForwardIdeal (K := K) G Q hAlt).hom X Y) :
    IsRadicalMorphism f := by
  apply isRadicalMorphism_of_forall_comp_isNilpotent f
  intro g
  apply isNilpotent_end_of_hasGap_one G Q hAlt
  change HasGap (K := K) G Q hAlt 1 f at hf
  simpa using hf.comp G Q hAlt
    (hasGap_zero_of_directed G Q hAlt g)

/-- Every nonzero endomorphism of a singleton word vertex is invertible. -/
theorem vertexEnd_isIso_of_ne_zero
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (x : Fin Q.length)
    (a : End (vertexObj (K := K) G Q hAlt x))
    (ha : a ≠ 0) : IsIso a := by
  rw [← CategoryTheory.isUnit_iff_isIso]
  let e := vertexSelfHomRingEquiv (K := K) G Q hAlt x
  have hea : e a ≠ 0 := by
    intro hzero
    apply ha
    exact e.injective (by simpa [e] using hzero)
  have hu : IsUnit (e a) := isUnit_iff_ne_zero.mpr hea
  simpa [e] using hu.map e.symm.toMonoidHom

/-- A radical endomorphism vanishes if every nonzero endomorphism of its
object is invertible. -/
theorem radicalEnd_eq_zero_of_nonzero_isIso
    {C : Type*} [CategoryTheory.Category C] [Preadditive C]
    {P : C} (hP : ∀ a : End P, a ≠ 0 → IsIso a)
    (a : End P) (ha : IsRadicalMorphism a) : a = 0 := by
  by_contra hane
  letI : IsIso a := hP a hane
  letI : IsIso (0 : P ⟶ P) := by
    convert ha (inv a) using 1
    all_goals simp
  have hid : (𝟙 P : P ⟶ P) = 0 := by
    rw [← cancel_mono (0 : P ⟶ P)]
    simp
  apply hane
  rw [← Category.comp_id a, hid, comp_zero]
  rfl

/-- Inclusion of one displayed matrix summand. -/
def entryInclusion
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    (X : Category (K := K) G Q hAlt) (i : X.ι) :
    (Mat_.embedding (WordMesh.Category (K := K) G Q hAlt)).obj
      (X.X i) ⟶ X := by
  exact fun _ k ↦ (𝟙 X) i k

/-- Projection onto one displayed matrix summand. -/
def entryProjection
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    (X : Category (K := K) G Q hAlt) (i : X.ι) :
    X ⟶ (Mat_.embedding (WordMesh.Category (K := K) G Q hAlt)).obj
      (X.X i) := by
  exact fun k _ ↦ (𝟙 X) k i

/-- Cutting a matrix morphism down to displayed singleton summands recovers
the corresponding matrix entry. -/
theorem entryInclusion_comp_comp_entryProjection
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    {X Y : Category (K := K) G Q hAlt}
    (f : X ⟶ Y) (i : X.ι) (j : Y.ι) :
    entryInclusion (K := K) G Q hAlt X i ≫ f ≫
        entryProjection (K := K) G Q hAlt Y j =
      (Mat_.embedding (WordMesh.Category (K := K) G Q hAlt)).map (f i j) := by
  classical
  apply Mat_.hom_ext
  intro u v
  cases u
  cases v
  change ((𝟙 X ≫ f ≫ 𝟙 Y) i j) = f i j
  rw [Category.comp_id]
  exact congrFun (congrFun (Category.id_comp f) i) j

set_option maxHeartbeats 1000000 in
/-- A categorical-radical matrix has zero entries between equal word
vertices. -/
theorem equal_entries_zero_of_isRadicalMorphism
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    {X Y : Category (K := K) G Q hAlt}
    (f : X ⟶ Y) (hf : IsRadicalMorphism f) :
    ∀ i j, X.X i = Y.X j → f i j = 0 := by
  intro i j hij
  have hpre : IsRadicalMorphism
      (entryInclusion (K := K) G Q hAlt X i ≫ f) :=
    isRadicalMorphism_precomp _ hf
  have hcomponent : IsRadicalMorphism
      (entryInclusion (K := K) G Q hAlt X i ≫ f ≫
        entryProjection (K := K) G Q hAlt Y j) :=
    by
      simpa only [Category.assoc] using
        (isRadicalMorphism_postcomp
          (f := entryInclusion (K := K) G Q hAlt X i ≫ f)
          (entryProjection (K := K) G Q hAlt Y j) hpre)
  rw [entryInclusion_comp_comp_entryProjection] at hcomponent
  let e : Y.X j ⟶ X.X i := eqToHom hij.symm
  let em := (Mat_.embedding
    (WordMesh.Category (K := K) G Q hAlt)).map e
  letI : IsIso e := by
    dsimp only [e]
    infer_instance
  letI : IsIso em := by
    dsimp only [em]
    infer_instance
  have hend : IsRadicalMorphism
      ((Mat_.embedding (WordMesh.Category (K := K) G Q hAlt)).map (f i j) ≫ em) :=
    isRadicalMorphism_postcomp em hcomponent
  have hzero := radicalEnd_eq_zero_of_nonzero_isIso
    (vertexEnd_isIso_of_ne_zero (K := K) G Q hAlt (X.X i))
    ((Mat_.embedding (WordMesh.Category (K := K) G Q hAlt)).map (f i j) ≫ em)
    hend
  change ((Mat_.embedding
    (WordMesh.Category (K := K) G Q hAlt)).map (f i j) ≫ em :
      (Mat_.embedding (WordMesh.Category (K := K) G Q hAlt)).obj (X.X i) ⟶
        (Mat_.embedding (WordMesh.Category (K := K) G Q hAlt)).obj (X.X i)) = 0
    at hzero
  have hcomponentZero :
      (Mat_.embedding (WordMesh.Category (K := K) G Q hAlt)).map (f i j) = 0 := by
    rw [← cancel_mono em]
    simpa only [zero_comp] using hzero
  exact (Mat_.embedding
    (WordMesh.Category (K := K) G Q hAlt)).map_injective
      (by simpa using hcomponentZero)

/-- The strictly-forward ideal is exactly the categorical radical. -/
theorem mem_strictForwardIdeal_iff_isRadicalMorphism
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    {X Y : Category (K := K) G Q hAlt}
    (f : X ⟶ Y) :
    f ∈ (strictForwardIdeal (K := K) G Q hAlt).hom X Y ↔
      IsRadicalMorphism f := by
  constructor
  · exact isRadicalMorphism_of_mem_strictForwardIdeal G Q hAlt f
  · intro hf
    exact (mem_strictForwardIdeal_iff_equal_entries_zero G Q hAlt f).2
      (equal_entries_zero_of_isRadicalMorphism G Q hAlt f hf)

/-- Nilpotent categorical-radical data for the abstract word-mesh additive
hull.  The chosen radical is the strictly-forward matrix ideal, and its
`Q.length`th power vanishes. -/
def nilpotentRadicalData
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) :
    NilpotentRadicalData (Category (K := K) G Q hAlt) where
  ideal := strictForwardIdeal (K := K) G Q hAlt
  mem_iff := mem_strictForwardIdeal_iff_isRadicalMorphism G Q hAlt
  nilpotent := strictForwardIdeal_isNilpotent G Q hAlt

end OpConjecture.RepresentationDirected.IyamaMesh.WordMesh.AdditiveHull
