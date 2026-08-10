import OpConjecture.RepresentationTheory.SeparatedTriangularAlgebra

/-!
# Separated data are modules over the triangular separated algebra

The two diagonal idempotents of `(S × S) ⋉ J` split every module into its
top and radical-side summands.  The square-zero ideal acts from the top
summand to the radical summand.  This gives the inverse object construction
to `SeparatedTriangularAlgebra.realizationFunctor` and proves that the latter
is an equivalence of categories.
-/

set_option autoImplicit false

noncomputable section

open scoped RightActions
open CategoryTheory

namespace OpConjecture.SeparatedTriangularAlgebra

open TrivSqZeroExtSeparatedData

universe u v w

variable {S : Type u} {J : Type v}
variable [CommRing S] [AddCommGroup J]
variable [Module S J] [Module Sᵐᵒᵖ J]
variable [SMulCommClass S Sᵐᵒᵖ J]

/-- The diagonal idempotent selecting the top side. -/
def topIdempotent : Algebra S J :=
  TrivSqZeroExt.inl (0, 1)

/-- The diagonal idempotent selecting the radical side. -/
def radicalIdempotent : Algebra S J :=
  TrivSqZeroExt.inl (1, 0)

/-- Scalar multiplication on the top side, viewed inside the triangular
algebra. -/
def topScalar (s : S) : Algebra S J :=
  TrivSqZeroExt.inl (0, s)

/-- Scalar multiplication on the radical side, viewed inside the triangular
algebra. -/
def radicalScalar (s : S) : Algebra S J :=
  TrivSqZeroExt.inl (s, 0)

private theorem algebra_ext
    {x y : Algebra S J} (hfst : x.fst = y.fst)
    (hsnd : x.snd.val = y.snd.val) : x = y := by
  apply Prod.ext
  · exact hfst
  · exact SeparatedIdeal.ext hsnd

@[simp]
theorem topIdempotent_mul_self :
    (topIdempotent : Algebra S J) * topIdempotent = topIdempotent := by
  apply algebra_ext <;> simp [topIdempotent]

@[simp]
theorem radicalIdempotent_mul_self :
    (radicalIdempotent : Algebra S J) * radicalIdempotent =
      radicalIdempotent := by
  apply algebra_ext <;> simp [radicalIdempotent]

@[simp]
theorem topIdempotent_add_radicalIdempotent :
    (topIdempotent : Algebra S J) + radicalIdempotent = 1 := by
  apply algebra_ext <;> simp [topIdempotent, radicalIdempotent]

@[simp]
theorem topIdempotent_mul_topScalar (s : S) :
    (topIdempotent : Algebra S J) * topScalar s = topScalar s := by
  apply algebra_ext <;> simp [topIdempotent, topScalar]

@[simp]
theorem radicalIdempotent_mul_radicalScalar (s : S) :
    (radicalIdempotent : Algebra S J) * radicalScalar s =
      radicalScalar s := by
  apply algebra_ext <;> simp [radicalIdempotent, radicalScalar]

@[simp]
theorem topScalar_add (s t : S) :
    topScalar (s + t) =
      (topScalar s : Algebra S J) + topScalar t := by
  apply algebra_ext <;> simp [topScalar]

@[simp]
theorem radicalScalar_add (s t : S) :
    radicalScalar (s + t) =
      (radicalScalar s : Algebra S J) + radicalScalar t := by
  apply algebra_ext <;> simp [radicalScalar]

@[simp]
theorem topScalar_mul (s t : S) :
    topScalar (s * t) =
      (topScalar s : Algebra S J) * topScalar t := by
  apply algebra_ext <;> simp [topScalar]

@[simp]
theorem radicalScalar_mul (s t : S) :
    radicalScalar (s * t) =
      (radicalScalar s : Algebra S J) * radicalScalar t := by
  apply algebra_ext <;> simp [radicalScalar]

@[simp]
theorem radicalScalar_mul_topIdempotent (s : S) :
    (radicalScalar s : Algebra S J) * topIdempotent = 0 := by
  apply algebra_ext <;> simp [radicalScalar, topIdempotent]

@[simp]
theorem topScalar_mul_radicalIdempotent (s : S) :
    (topScalar s : Algebra S J) * radicalIdempotent = 0 := by
  apply algebra_ext <;> simp [topScalar, radicalIdempotent]

@[simp]
theorem topIdempotent_mul_radicalIdempotent :
    (topIdempotent : Algebra S J) * radicalIdempotent = 0 := by
  apply algebra_ext <;> simp [topIdempotent, radicalIdempotent]

@[simp]
theorem radicalIdempotent_mul_topIdempotent :
    (radicalIdempotent : Algebra S J) * topIdempotent = 0 := by
  apply algebra_ext <;> simp [topIdempotent, radicalIdempotent]

@[simp]
theorem radicalIdempotent_mul_inr (j : J) :
    (radicalIdempotent : Algebra S J) *
        TrivSqZeroExt.inr (⟨j⟩ : SeparatedIdeal S J) =
      TrivSqZeroExt.inr ⟨j⟩ := by
  change TrivSqZeroExt.inl ((1, 0) : S × S) *
      TrivSqZeroExt.inr (⟨j⟩ : SeparatedIdeal S J) =
    TrivSqZeroExt.inr ⟨j⟩
  rw [TrivSqZeroExt.inl_mul_inr]
  congr 1
  apply SeparatedIdeal.ext
  change (1 : S) • j = j
  exact one_smul S j

@[simp]
theorem inr_mul_radicalIdempotent (j : J) :
    (TrivSqZeroExt.inr (⟨j⟩ : SeparatedIdeal S J) : Algebra S J) *
        radicalIdempotent = 0 := by
  change TrivSqZeroExt.inr (⟨j⟩ : SeparatedIdeal S J) *
      TrivSqZeroExt.inl ((1, 0) : S × S) = 0
  rw [TrivSqZeroExt.inr_mul_inl]
  change TrivSqZeroExt.inr
      ((⟨j⟩ : SeparatedIdeal S J) <• ((1, 0) : S × S)) = 0
  rw [show ((⟨j⟩ : SeparatedIdeal S J) <• ((1, 0) : S × S)) = 0 by
    apply SeparatedIdeal.ext
    exact zero_smul Sᵐᵒᵖ j]
  exact TrivSqZeroExt.inr_zero (S × S)

@[simp]
theorem radicalScalar_mul_inr (s : S) (j : J) :
    (radicalScalar s : Algebra S J) *
        TrivSqZeroExt.inr (⟨j⟩ : SeparatedIdeal S J) =
      TrivSqZeroExt.inr ⟨s • j⟩ := by
  change TrivSqZeroExt.inl ((s, 0) : S × S) *
      TrivSqZeroExt.inr (⟨j⟩ : SeparatedIdeal S J) =
    TrivSqZeroExt.inr ⟨s • j⟩
  rw [TrivSqZeroExt.inl_mul_inr]
  congr 1

@[simp]
theorem inr_mul_topScalar (j : J) (s : S) :
    (TrivSqZeroExt.inr (⟨j⟩ : SeparatedIdeal S J) : Algebra S J) *
        topScalar s = TrivSqZeroExt.inr ⟨j <• s⟩ := by
  change TrivSqZeroExt.inr (⟨j⟩ : SeparatedIdeal S J) *
      TrivSqZeroExt.inl ((0, s) : S × S) =
    TrivSqZeroExt.inr ⟨j <• s⟩
  rw [TrivSqZeroExt.inr_mul_inl]
  congr 1

/-- Every triangular-algebra element is the sum of its two diagonal scalar
parts and its square-zero part. -/
theorem scalar_decomposition (sRad sTop : S) (j : J) :
    ((sRad, sTop), (⟨j⟩ : SeparatedIdeal S J)) =
      (radicalScalar sRad : Algebra S J) + topScalar sTop +
        TrivSqZeroExt.inr ⟨j⟩ := by
  apply TrivSqZeroExt.ext
  · change (sRad, sTop) =
      (sRad, 0) + (0, sTop) + (0 : S × S)
    ext <;> simp
  · change (⟨j⟩ : SeparatedIdeal S J) = 0 + 0 + ⟨j⟩
    simp

variable (X : ModuleCat.{w} (Algebra S J))

/-- The elements fixed by the top idempotent. -/
def topPartAddSubgroup : AddSubgroup X where
  carrier := {x | (topIdempotent : Algebra S J) • x = x}
  zero_mem' := by
    change (topIdempotent : Algebra S J) • (0 : X) = 0
    exact smul_zero _
  add_mem' := by
    intro x y hx hy
    change (topIdempotent : Algebra S J) • (x + y) = x + y
    change (topIdempotent : Algebra S J) • x = x at hx
    change (topIdempotent : Algebra S J) • y = y at hy
    rw [smul_add, hx, hy]
  neg_mem' := by
    intro x hx
    change (topIdempotent : Algebra S J) • (-x) = -x
    change (topIdempotent : Algebra S J) • x = x at hx
    rw [smul_neg, hx]

/-- The elements fixed by the radical-side idempotent. -/
def radicalPartAddSubgroup : AddSubgroup X where
  carrier := {x | (radicalIdempotent : Algebra S J) • x = x}
  zero_mem' := by
    change (radicalIdempotent : Algebra S J) • (0 : X) = 0
    exact smul_zero _
  add_mem' := by
    intro x y hx hy
    change (radicalIdempotent : Algebra S J) • (x + y) = x + y
    change (radicalIdempotent : Algebra S J) • x = x at hx
    change (radicalIdempotent : Algebra S J) • y = y at hy
    rw [smul_add, hx, hy]
  neg_mem' := by
    intro x hx
    change (radicalIdempotent : Algebra S J) • (-x) = -x
    change (radicalIdempotent : Algebra S J) • x = x at hx
    rw [smul_neg, hx]

/-- The top-idempotent summand of a triangular-algebra module. -/
abbrev TopPart := ↥(topPartAddSubgroup (S := S) (J := J) X)

/-- The radical-idempotent summand of a triangular-algebra module. -/
abbrev RadicalPart := ↥(radicalPartAddSubgroup (S := S) (J := J) X)

@[simp]
theorem topPart_fixed (x : TopPart (S := S) (J := J) X) :
    (topIdempotent : Algebra S J) • x.val = x.val := by
  have h := x.property
  change (topIdempotent : Algebra S J) • x.val = x.val at h
  exact h

@[simp]
theorem radicalPart_fixed (x : RadicalPart (S := S) (J := J) X) :
    (radicalIdempotent : Algebra S J) • x.val = x.val := by
  have h := x.property
  change (radicalIdempotent : Algebra S J) • x.val = x.val at h
  exact h

instance topPartSMul : SMul S (TopPart (S := S) (J := J) X) where
  smul s x :=
    ⟨(topScalar (S := S) (J := J) s : Algebra S J) • x.val, by
      change (topIdempotent : Algebra S J) •
          ((topScalar (S := S) (J := J) s : Algebra S J) • x.val) =
        (topScalar (S := S) (J := J) s : Algebra S J) • x.val
      rw [← mul_smul, topIdempotent_mul_topScalar]⟩

instance topPartModule : Module S (TopPart (S := S) (J := J) X) :=
  Module.ofMinimalAxioms
    (by
      intro s x y
      apply Subtype.ext
      exact smul_add (topScalar s) x.val y.val)
    (by
      intro s t x
      apply Subtype.ext
      change topScalar (s + t) • x.val =
        topScalar s • x.val + topScalar t • x.val
      rw [topScalar_add, add_smul])
    (by
      intro s t x
      apply Subtype.ext
      change topScalar (s * t) • x.val =
        topScalar s • (topScalar t • x.val)
      rw [topScalar_mul, mul_smul])
    (by
      intro x
      apply Subtype.ext
      change (topIdempotent : Algebra S J) • x.val = x.val
      exact x.property)

instance radicalPartSMul : SMul S (RadicalPart (S := S) (J := J) X) where
  smul s x :=
    ⟨(radicalScalar (S := S) (J := J) s : Algebra S J) • x.val, by
      change (radicalIdempotent : Algebra S J) •
          ((radicalScalar (S := S) (J := J) s : Algebra S J) • x.val) =
        (radicalScalar (S := S) (J := J) s : Algebra S J) • x.val
      rw [← mul_smul, radicalIdempotent_mul_radicalScalar]⟩

instance radicalPartModule :
    Module S (RadicalPart (S := S) (J := J) X) :=
  Module.ofMinimalAxioms
    (by
      intro s x y
      apply Subtype.ext
      exact smul_add (radicalScalar s) x.val y.val)
    (by
      intro s t x
      apply Subtype.ext
      change radicalScalar (s + t) • x.val =
        radicalScalar s • x.val + radicalScalar t • x.val
      rw [radicalScalar_add, add_smul])
    (by
      intro s t x
      apply Subtype.ext
      change radicalScalar (s * t) • x.val =
        radicalScalar s • (radicalScalar t • x.val)
      rw [radicalScalar_mul, mul_smul])
    (by
      intro x
      apply Subtype.ext
      change (radicalIdempotent : Algebra S J) • x.val = x.val
      exact x.property)

/-- The square-zero ideal acts from the top-idempotent summand into the
radical-idempotent summand. -/
def moduleSeparatedAction :
    J →+ (TopPart (S := S) (J := J) X →+
      RadicalPart (S := S) (J := J) X) where
  toFun j :=
    { toFun := fun t ↦
        ⟨(TrivSqZeroExt.inr (⟨j⟩ : SeparatedIdeal S J) : Algebra S J) •
            t.val, by
          change (radicalIdempotent : Algebra S J) •
              ((TrivSqZeroExt.inr (⟨j⟩ : SeparatedIdeal S J) :
                Algebra S J) • t.val) =
            (TrivSqZeroExt.inr (⟨j⟩ : SeparatedIdeal S J) :
                Algebra S J) • t.val
          rw [← mul_smul, radicalIdempotent_mul_inr]⟩
      map_zero' := by
        apply Subtype.ext
        simp
      map_add' := by
        intro t u
        apply Subtype.ext
        exact smul_add
          (TrivSqZeroExt.inr (⟨j⟩ : SeparatedIdeal S J) : Algebra S J)
          t.val u.val }
  map_zero' := by
    ext t
    change (TrivSqZeroExt.inr (⟨0⟩ : SeparatedIdeal S J) : Algebra S J) •
      t.val = 0
    rw [show (⟨0⟩ : SeparatedIdeal S J) = 0 by
      apply SeparatedIdeal.ext
      rfl]
    rw [TrivSqZeroExt.inr_zero, zero_smul]
  map_add' := by
    intro j k
    ext t
    change (TrivSqZeroExt.inr (⟨j + k⟩ : SeparatedIdeal S J) :
        Algebra S J) • t.val =
      (TrivSqZeroExt.inr (⟨j⟩ : SeparatedIdeal S J) : Algebra S J) •
          t.val +
      (TrivSqZeroExt.inr (⟨k⟩ : SeparatedIdeal S J) : Algebra S J) •
          t.val
    rw [show (⟨j + k⟩ : SeparatedIdeal S J) = ⟨j⟩ + ⟨k⟩ by
      apply SeparatedIdeal.ext
      rfl]
    rw [TrivSqZeroExt.inr_add, add_smul]

theorem moduleSeparatedAction_left_smul (s : S) (j : J)
    (t : TopPart (S := S) (J := J) X) :
    moduleSeparatedAction (S := S) (J := J) X (s • j) t =
      s • moduleSeparatedAction (S := S) (J := J) X j t := by
  apply Subtype.ext
  change (TrivSqZeroExt.inr (⟨s • j⟩ : SeparatedIdeal S J) :
      Algebra S J) • t.val =
    radicalScalar s •
      ((TrivSqZeroExt.inr (⟨j⟩ : SeparatedIdeal S J) : Algebra S J) •
        t.val)
  rw [← mul_smul, radicalScalar_mul_inr]

theorem moduleSeparatedAction_right_smul (j : J) (s : S)
    (t : TopPart (S := S) (J := J) X) :
    moduleSeparatedAction (S := S) (J := J) X (j <• s) t =
      moduleSeparatedAction (S := S) (J := J) X j (s • t) := by
  apply Subtype.ext
  change (TrivSqZeroExt.inr (⟨j <• s⟩ : SeparatedIdeal S J) :
      Algebra S J) • t.val =
    (TrivSqZeroExt.inr (⟨j⟩ : SeparatedIdeal S J) : Algebra S J) •
      (topScalar s • t.val)
  rw [← mul_smul, inr_mul_topScalar]

/-- The separated datum extracted from a triangular-algebra module. -/
abbrev ofModule : SeparatedData.{u, v, w} (S := S) (J := J) where
  top := ModuleCat.of S (TopPart (S := S) (J := J) X)
  radical := ModuleCat.of S (RadicalPart (S := S) (J := J) X)
  action := moduleSeparatedAction (S := S) (J := J) X
  action_left_smul := moduleSeparatedAction_left_smul X
  action_right_smul := moduleSeparatedAction_right_smul X

theorem radicalScalar_smul_top_eq_zero (s : S)
    (t : TopPart (S := S) (J := J) X) :
    (radicalScalar s : Algebra S J) • t.val = 0 := by
  rw [← topPart_fixed X t, ← mul_smul, radicalScalar_mul_topIdempotent,
    zero_smul]

theorem topScalar_smul_radical_eq_zero (s : S)
    (d : RadicalPart (S := S) (J := J) X) :
    (topScalar s : Algebra S J) • d.val = 0 := by
  rw [← radicalPart_fixed X d, ← mul_smul, topScalar_mul_radicalIdempotent,
    zero_smul]

theorem inr_smul_radical_eq_zero (j : J)
    (d : RadicalPart (S := S) (J := J) X) :
    (TrivSqZeroExt.inr (⟨j⟩ : SeparatedIdeal S J) : Algebra S J) •
      d.val = 0 := by
  rw [← radicalPart_fixed X d, ← mul_smul,
    inr_mul_radicalIdempotent, zero_smul]

theorem topIdempotent_smul_radical_eq_zero
    (d : RadicalPart (S := S) (J := J) X) :
    (topIdempotent : Algebra S J) • d.val = 0 := by
  rw [← radicalPart_fixed X d, ← mul_smul,
    topIdempotent_mul_radicalIdempotent,
    zero_smul]

theorem radicalIdempotent_smul_top_eq_zero
    (t : TopPart (S := S) (J := J) X) :
    (radicalIdempotent : Algebra S J) • t.val = 0 := by
  rw [← topPart_fixed X t, ← mul_smul,
    radicalIdempotent_mul_topIdempotent,
    zero_smul]

instance ofModuleRealizedSMul :
    SMul (Algebra S J) (Realized (ofModule (S := S) (J := J) X)) :=
  realizedSMul (ofModule (S := S) (J := J) X)

instance ofModuleRealizedModule :
    Module (Algebra S J) (Realized (ofModule (S := S) (J := J) X)) :=
  realizedModule (S := S) (J := J)
    (ofModule (S := S) (J := J) X)

/-- Add the two idempotent summands back into the original module. -/
def sumLinearMap :
    Realized (ofModule (S := S) (J := J) X) →ₗ[Algebra S J] X where
  toFun x := x.1.val + x.2.val
  map_add' := by
    intro x y
    change (x.1.val + y.1.val) + (x.2.val + y.2.val) =
      (x.1.val + x.2.val) + (y.1.val + y.2.val)
    abel
  map_smul' := by
    intro r x
    rcases x with ⟨t, d⟩
    change TopPart (S := S) (J := J) X at t
    change RadicalPart (S := S) (J := J) X at d
    change topScalar r.fst.2 • t.val +
        (radicalScalar r.fst.1 • d.val +
          (TrivSqZeroExt.inr (⟨r.snd.val⟩ : SeparatedIdeal S J) :
            Algebra S J) • t.val) =
      r • (t.val + d.val)
    have hr : r =
        (radicalScalar r.fst.1 : Algebra S J) + topScalar r.fst.2 +
          TrivSqZeroExt.inr ⟨r.snd.val⟩ := by
      rcases r with ⟨⟨sRad, sTop⟩, ⟨j⟩⟩
      exact scalar_decomposition sRad sTop j
    conv_rhs => rw [hr]
    rw [add_smul, add_smul, smul_add, smul_add,
      smul_add, radicalScalar_smul_top_eq_zero X,
      topScalar_smul_radical_eq_zero X, inr_smul_radical_eq_zero X]
    abel

@[simp]
theorem sumLinearMap_apply
    (x : Realized (ofModule (S := S) (J := J) X)) :
    sumLinearMap (S := S) (J := J) X x = x.1.val + x.2.val := rfl

/-- The summation map is bijective because the two diagonal idempotents are
orthogonal and sum to one. -/
theorem sumLinearMap_bijective :
    Function.Bijective (sumLinearMap (S := S) (J := J) X) := by
  constructor
  · intro x y h
    rcases x with ⟨tx, dx⟩
    rcases y with ⟨ty, dy⟩
    rw [sumLinearMap_apply, sumLinearMap_apply] at h
    apply Prod.ext
    · apply Subtype.ext
      have ht := congrArg
        (fun z : X ↦ (topIdempotent : Algebra S J) • z) h
      simpa only [smul_add, topPart_fixed X,
        topIdempotent_smul_radical_eq_zero X, add_zero] using ht
    · apply Subtype.ext
      have hd := congrArg
        (fun z : X ↦ (radicalIdempotent : Algebra S J) • z) h
      simpa only [smul_add, radicalPart_fixed X,
        radicalIdempotent_smul_top_eq_zero X, zero_add] using hd
  · intro x
    let t : TopPart (S := S) (J := J) X :=
      ⟨(topIdempotent : Algebra S J) • x, by
        change (topIdempotent : Algebra S J) •
            ((topIdempotent : Algebra S J) • x) =
          (topIdempotent : Algebra S J) • x
        rw [← mul_smul, topIdempotent_mul_self]⟩
    let d : RadicalPart (S := S) (J := J) X :=
      ⟨(radicalIdempotent : Algebra S J) • x, by
        change (radicalIdempotent : Algebra S J) •
            ((radicalIdempotent : Algebra S J) • x) =
          (radicalIdempotent : Algebra S J) • x
        rw [← mul_smul, radicalIdempotent_mul_self]⟩
    refine ⟨(t, d), ?_⟩
    dsimp only [sumLinearMap, t, d]
    change (topIdempotent : Algebra S J) • x +
      (radicalIdempotent : Algebra S J) • x = x
    rw [← add_smul, topIdempotent_add_radicalIdempotent, one_smul]

/-- Realizing the separated datum extracted from a module recovers that
module. -/
def realizedOfModuleIso :
    (realizationFunctor (S := S) (J := J)).obj
        (ofModule (S := S) (J := J) X) ≅ X :=
  LinearEquiv.toModuleIso
    (LinearEquiv.ofBijective (sumLinearMap (S := S) (J := J) X)
      (sumLinearMap_bijective (S := S) (J := J) X))

instance realizationFunctor_essSurj :
    (realizationFunctor (S := S) (J := J)).EssSurj where
  mem_essImage X :=
    ⟨ofModule (S := S) (J := J) X,
      ⟨realizedOfModuleIso (S := S) (J := J) X⟩⟩

instance realizationFunctor_isEquivalence :
    (realizationFunctor (S := S) (J := J)).IsEquivalence where

/-- Abstract separated data are categorically equivalent to modules over
the triangular separated algebra. -/
def moduleEquivalence :
    SeparatedData.{u, v, w} (S := S) (J := J) ≌
      ModuleCat.{w} (Algebra S J) :=
  (realizationFunctor (S := S) (J := J)).asEquivalence

end OpConjecture.SeparatedTriangularAlgebra
