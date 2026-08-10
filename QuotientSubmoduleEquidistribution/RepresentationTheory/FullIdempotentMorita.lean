import QuotientSubmoduleEquidistribution.RepresentationTheory.MoritaBasicizationExistence
import Mathlib.LinearAlgebra.FixedSubmodule
import Mathlib.CategoryTheory.Equivalence

/-!
# Full-idempotent Morita equivalence

A full idempotent `e` gives an explicit `K`-linear equivalence between
left modules over `A` and over the corner `eAe`.  The construction uses a
finite fullness frame, the fixed-space functor `M ↦ eM`, and a finite frame
module for essential surjectivity.  Combining this categorical bridge with
the ring-theoretic idempotent construction makes finite-dimensional Morita
basicization unconditional over an algebraically closed field.
-/

noncomputable section

open CategoryTheory
open scoped ModuleCat.Algebra

namespace QuotientSubmoduleEquidistribution.FullIdempotentMorita

universe u

variable {K A : Type u}
  [Field K] [Ring A] [Algebra K A]
variable {e : A} (he : IsIdempotentElem e)

open QuotientSubmoduleEquidistribution.MoritaBasicizationInterface

local instance : Algebra K he.Corner := cornerAlgebra (K := K) he

/-- Additive inclusion of the corner into the ambient ring. -/
def cornerValAddHom : he.Corner →+ A where
  toFun c := c.1
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem cornerValAddHom_apply (c : he.Corner) :
    cornerValAddHom he c = c.1 := rfl

@[simp]
theorem corner_add_val (c d : he.Corner) : (c + d).1 = c.1 + d.1 := rfl

@[simp]
theorem corner_zero_val : (0 : he.Corner).1 = (0 : A) := rfl

/-- Multiplication by `e` on a left `A`-module, viewed as a `K`-linear idempotent. -/
def cornerProjection (M : ModuleCat.{u} A) : M →ₗ[K] M where
  toFun m := e • m
  map_add' := smul_add e
  map_smul' k m := by
    change e • (algebraMap K A k • m) = algebraMap K A k • (e • m)
    rw [← mul_smul, ← mul_smul, Algebra.commutes k e]

theorem cornerProjection_idempotent (he : IsIdempotentElem e) (M : ModuleCat.{u} A) :
    IsIdempotentElem (cornerProjection (K := K) (e := e) M) := by
  rw [IsIdempotentElem]
  ext m
  simp [cornerProjection, Module.End.mul_apply, ← mul_smul, he.eq]

/-- The fixed space `eM`, as a `K`-subspace. -/
abbrev CornerPart (M : ModuleCat.{u} A) : Type u :=
  (cornerProjection (K := K) (e := e) M).fixedSubmodule

/-- The natural left `eAe`-action on `eM`. -/
instance cornerPartModule (M : ModuleCat.{u} A) :
    Module he.Corner (CornerPart (K := K) (e := e) M) where
  smul c m := ⟨c.1 • m.1, by
    change e • (c.1 • m.1) = c.1 • m.1
    rw [← mul_smul]
    have hc := (Subsemigroup.mem_corner_iff he).mp c.property
    rw [hc.1]⟩
  one_smul m := by
    apply Subtype.ext
    exact m.property
  mul_smul c d m := by
    apply Subtype.ext
    exact mul_smul c.1 d.1 m.1
  zero_smul m := by
    apply Subtype.ext
    exact zero_smul A m.1
  add_smul c d m := by
    apply Subtype.ext
    exact add_smul c.1 d.1 m.1
  smul_zero c := by
    apply Subtype.ext
    exact smul_zero c.1
  smul_add c m n := by
    apply Subtype.ext
    exact smul_add c.1 m.1 n.1

@[simp]
theorem cornerPart_smul_val (M : ModuleCat.{u} A) (c : he.Corner)
    (m : CornerPart (K := K) (e := e) M) :
    (c • m).1 = c.1 • m.1 := rfl

/-- Restriction of an `A`-linear map to corner fixed spaces. -/
def cornerPartMap {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    CornerPart (K := K) (e := e) M →ₗ[he.Corner]
      CornerPart (K := K) (e := e) N where
  toFun m := ⟨f m.1, by
    change e • f m.1 = f m.1
    rw [← f.hom.map_smul]
    have hm := m.property
    change e • m.1 = m.1 at hm
    rw [hm]⟩
  map_add' _ _ := by ext; exact f.hom.map_add _ _
  map_smul' c m := by
    apply Subtype.ext
    exact f.hom.map_smul c.1 m.1

/-- The corner fixed-space functor. -/
def cornerFunctor : ModuleCat.{u} A ⥤ ModuleCat.{u} he.Corner where
  obj M := ModuleCat.of he.Corner (CornerPart (K := K) (e := e) M)
  map f := ModuleCat.ofHom (cornerPartMap (K := K) he f)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- A chosen finite presentation of the fullness equation `1 ∈ AeA`. -/
structure FullFrame (e : A) where
  n : ℕ
  left : Fin n → A
  right : Fin n → A
  complete : ∑ i, left i * e * right i = 1

/-- Choice of a finite frame from elementwise fullness. -/
def FullFrame.ofFull (hfull : IsFullElem e) : FullFrame e :=
  ⟨hfull.choose, hfull.choose_spec.choose,
    hfull.choose_spec.choose_spec.choose,
    hfull.choose_spec.choose_spec.choose_spec⟩

/-- Project any vector to the corner fixed space. -/
def toCornerPart (M : ModuleCat.{u} A) (m : M) : CornerPart (K := K) (e := e) M :=
  ⟨e • m, by
    change e • (e • m) = e • m
    rw [← mul_smul, he.eq]⟩

@[simp]
theorem toCornerPart_val (M : ModuleCat.{u} A) (m : M) :
    (toCornerPart (K := K) he M m).1 = e • m := rfl

@[simp]
theorem toCornerPart_add (M : ModuleCat.{u} A) (m m' : M) :
    toCornerPart (K := K) he M (m + m') =
      toCornerPart (K := K) he M m + toCornerPart (K := K) he M m' := by
  ext
  exact smul_add e m m'

@[simp]
theorem toCornerPart_zero (M : ModuleCat.{u} A) :
    toCornerPart (K := K) he M 0 = 0 := by
  ext
  exact smul_zero e

/-- The explicit extension of a corner-linear map along a full frame. -/
def extendCornerHom (P : FullFrame e) {M N : ModuleCat.{u} A}
    (f : CornerPart (K := K) (e := e) M →ₗ[he.Corner]
      CornerPart (K := K) (e := e) N) : M →+ N where
  toFun m := ∑ i, P.left i •
    (f (toCornerPart (K := K) he M (P.right i • m))).1
  map_zero' := by
    apply Finset.sum_eq_zero
    intro i _
    have hi :
        (f (toCornerPart (K := K) he M (P.right i • (0 : M)))).1 = 0 := by
      rw [smul_zero, toCornerPart_zero]
      exact congrArg Subtype.val f.map_zero
    rw [hi, smul_zero]
  map_add' m m' := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hi :
        (f (toCornerPart (K := K) he M (P.right i • (m + m')))).1 =
          (f (toCornerPart (K := K) he M (P.right i • m))).1 +
          (f (toCornerPart (K := K) he M (P.right i • m'))).1 := by
      rw [smul_add, toCornerPart_add]
      exact congrArg Subtype.val (f.map_add _ _)
    rw [hi, smul_add]

@[simp]
theorem extendCornerHom_apply (P : FullFrame e) {M N : ModuleCat.{u} A}
    (f : CornerPart (K := K) (e := e) M →ₗ[he.Corner]
      CornerPart (K := K) (e := e) N) (m : M) :
    extendCornerHom (K := K) he P f m =
      ∑ i, P.left i •
        (f (toCornerPart (K := K) he M (P.right i • m))).1 := rfl

/-- The corner coefficient matrix describing multiplication by an ambient
element in a chosen full frame. -/
def frameCoeff (P : FullFrame e) (i : Fin P.n) (r : A) (j : Fin P.n) :
    he.Corner :=
  ⟨e * P.right i * r * P.left j * e, by
    apply (Subsemigroup.mem_corner_iff he).mpr
    constructor
    · simp only [← mul_assoc, he.eq]
    · simp only [mul_assoc, he.eq]⟩

@[simp]
theorem frameCoeff_val (P : FullFrame e) (i : Fin P.n) (r : A) (j : Fin P.n) :
    (frameCoeff he P i r j).1 = e * P.right i * r * P.left j * e := rfl

/-- The fullness equation gives the matrix reconstruction formula for the
corner components of `r • m`. -/
theorem toCornerPart_smul_frame (P : FullFrame e) (M : ModuleCat.{u} A)
    (i : Fin P.n) (r : A) (m : M) :
    toCornerPart (K := K) he M (P.right i • (r • m)) =
      ∑ j, frameCoeff he P i r j •
        toCornerPart (K := K) he M (P.right j • m) := by
  apply Subtype.ext
  change e • (P.right i • (r • m)) =
    ((↑(∑ j, frameCoeff he P i r j •
      toCornerPart (K := K) he M (P.right j • m)) : M))
  rw [Submodule.coe_sum]
  simp only [cornerPart_smul_val, frameCoeff_val, toCornerPart_val]
  simp only [← mul_smul]
  rw [← Finset.sum_smul]
  congr 1
  symm
  calc
    ∑ j, (e * P.right i * r * P.left j * e) * (e * P.right j) =
        (e * P.right i * r) * ∑ j, P.left j * e * P.right j := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          calc
            (e * P.right i * r * P.left j * e) * (e * P.right j) =
                (e * P.right i * r * P.left j) * (e * e) * P.right j := by
                  noncomm_ring
            _ = (e * P.right i * r * P.left j) * e * P.right j := by
                  rw [he.eq]
            _ = (e * P.right i * r) * (P.left j * e * P.right j) := by
                  noncomm_ring
    _ = e * P.right i * r := by rw [P.complete, mul_one]
    _ = e * (P.right i * r) := by rw [mul_assoc]

/-- The dual reconstruction formula: synthesis from the corner components
intertwines multiplication by every ambient algebra element. -/
theorem synthesis_smul_frame (P : FullFrame e) (N : ModuleCat.{u} A)
    (r : A) (j : Fin P.n) (y : CornerPart (K := K) (e := e) N) :
    r • (P.left j • y.1) =
      ∑ i, P.left i • ((frameCoeff he P i r j • y).1) := by
  simp only [cornerPart_smul_val, frameCoeff_val, ← mul_smul]
  rw [← Finset.sum_smul]
  have hscalar :
      ∑ i, P.left i * (e * P.right i * r * P.left j * e) =
        r * P.left j * e := by
    calc
      ∑ i, P.left i * (e * P.right i * r * P.left j * e) =
          (∑ i, P.left i * e * P.right i) * (r * P.left j * e) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _
            noncomm_ring
      _ = r * P.left j * e := by rw [P.complete, one_mul]
  rw [hscalar]
  simp only [mul_smul]
  have hy := y.property
  change e • y.1 = y.1 at hy
  rw [hy, ← mul_smul]

/-- A corner-linear map transports the analysis reconstruction formula. -/
theorem cornerHom_toCornerPart_smul_frame (P : FullFrame e)
    {M N : ModuleCat.{u} A}
    (f : CornerPart (K := K) (e := e) M →ₗ[he.Corner]
      CornerPart (K := K) (e := e) N)
    (i : Fin P.n) (r : A) (m : M) :
    (f (toCornerPart (K := K) he M (P.right i • (r • m)))).1 =
      ∑ j, (frameCoeff he P i r j •
        f (toCornerPart (K := K) he M (P.right j • m))).1 := by
  have h :
      f (toCornerPart (K := K) he M (P.right i • (r • m))) =
        ∑ j, frameCoeff he P i r j •
          f (toCornerPart (K := K) he M (P.right j • m)) := by
    rw [toCornerPart_smul_frame]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact f.map_smul _ _
  rw [h, Submodule.coe_sum]

/-- The explicit extension is genuinely `A`-linear. -/
theorem extendCornerHom_map_smul (P : FullFrame e) {M N : ModuleCat.{u} A}
    (f : CornerPart (K := K) (e := e) M →ₗ[he.Corner]
      CornerPart (K := K) (e := e) N) (r : A) (m : M) :
    extendCornerHom (K := K) he P f (r • m) =
      r • extendCornerHom (K := K) he P f m := by
  rw [extendCornerHom_apply, extendCornerHom_apply]
  simp_rw [cornerHom_toCornerPart_smul_frame]
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact (synthesis_smul_frame (K := K) he P N r j
    (f (toCornerPart (K := K) he M (P.right j • m)))).symm

/-- The bundled `A`-linear extension. -/
def liftCornerHom (P : FullFrame e) {M N : ModuleCat.{u} A}
    (f : CornerPart (K := K) (e := e) M →ₗ[he.Corner]
      CornerPart (K := K) (e := e) N) : M →ₗ[A] N where
  __ := extendCornerHom (K := K) he P f
  map_smul' := extendCornerHom_map_smul (K := K) he P f

/-- Extending the restriction of an ambient linear map recovers that map. -/
theorem lift_cornerPartMap_apply (P : FullFrame e) {M N : ModuleCat.{u} A}
    (g : M ⟶ N) (m : M) :
    liftCornerHom (K := K) he P (cornerPartMap (K := K) he g) m = g.hom m := by
  rw [show liftCornerHom (K := K) he P (cornerPartMap (K := K) he g) m =
      extendCornerHom (K := K) he P (cornerPartMap (K := K) he g) m from rfl]
  rw [extendCornerHom_apply]
  have hi (i : Fin P.n) :
      (cornerPartMap (K := K) he g
        (toCornerPart (K := K) he M (P.right i • m))).1 =
        (e * P.right i) • g.hom m := by
    change g.hom (e • (P.right i • m)) = (e * P.right i) • g.hom m
    rw [← mul_smul, g.hom.map_smul]
  simp_rw [hi]
  simp only [← mul_smul]
  rw [← Finset.sum_smul]
  have hscalar : ∑ i, P.left i * (e * P.right i) = 1 := by
    calc
      ∑ i, P.left i * (e * P.right i) =
          ∑ i, P.left i * e * P.right i := by
            apply Finset.sum_congr rfl
            intro i _
            rw [mul_assoc]
      _ = 1 := P.complete
  rw [hscalar, one_smul]

/-- The corner element that analyzes the `i`th frame component. -/
def frameRightCorner (P : FullFrame e) (i : Fin P.n) : he.Corner :=
  ⟨e * P.right i * e, by
    apply (Subsemigroup.mem_corner_iff he).mpr
    constructor
    · simp only [← mul_assoc, he.eq]
    · simp only [mul_assoc, he.eq]⟩

@[simp]
theorem frameRightCorner_val (P : FullFrame e) (i : Fin P.n) :
    (frameRightCorner he P i).1 = e * P.right i * e := rfl

/-- On an already fixed vector, ambient analysis is multiplication by a
corner element. -/
theorem toCornerPart_of_fixed (P : FullFrame e) (M : ModuleCat.{u} A)
    (i : Fin P.n) (y : CornerPart (K := K) (e := e) M) :
    toCornerPart (K := K) he M (P.right i • y.1) =
      frameRightCorner he P i • y := by
  apply Subtype.ext
  simp only [toCornerPart_val, cornerPart_smul_val, frameRightCorner_val]
  have hy := y.property
  change e • y.1 = y.1 at hy
  calc
    e • (P.right i • y.1) = (e * P.right i) • y.1 :=
      (mul_smul e (P.right i) y.1).symm
    _ = (e * P.right i) • (e • y.1) := by rw [hy]
    _ = (e * P.right i * e) • y.1 :=
      (mul_smul (e * P.right i) e y.1).symm

/-- Restricting the explicit extension recovers the original corner map. -/
theorem cornerPartMap_lift_apply (P : FullFrame e) {M N : ModuleCat.{u} A}
    (f : CornerPart (K := K) (e := e) M →ₗ[he.Corner]
      CornerPart (K := K) (e := e) N)
    (y : CornerPart (K := K) (e := e) M) :
    (cornerPartMap (K := K) he
      (ModuleCat.ofHom (liftCornerHom (K := K) he P f)) y) = f y := by
  apply Subtype.ext
  change liftCornerHom (K := K) he P f y.1 = (f y).1
  rw [show liftCornerHom (K := K) he P f y.1 =
      extendCornerHom (K := K) he P f y.1 from rfl]
  rw [extendCornerHom_apply]
  have hi (i : Fin P.n) :
      (f (toCornerPart (K := K) he M (P.right i • y.1))).1 =
        ((frameRightCorner he P i) • f y).1 := by
    rw [toCornerPart_of_fixed]
    exact congrArg Subtype.val (f.map_smul _ _)
  simp_rw [hi, cornerPart_smul_val, frameRightCorner_val]
  simp only [← mul_smul]
  rw [← Finset.sum_smul]
  have hscalar :
      ∑ i, P.left i * (e * P.right i * e) = e := by
    calc
      ∑ i, P.left i * (e * P.right i * e) =
          (∑ i, P.left i * e * P.right i) * e := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _
            noncomm_ring
      _ = e := by rw [P.complete, one_mul]
  rw [hscalar]
  have hfy := (f y).property
  change e • (f y).1 = (f y).1 at hfy
  exact hfy

/-- Full faithfulness of the corner fixed-space functor, with an explicit
preimage on every hom space. -/
def cornerFunctorFullyFaithful (P : FullFrame e) :
    (cornerFunctor (K := K) he).FullyFaithful where
  preimage {M N} f :=
    ModuleCat.ofHom <| liftCornerHom (K := K) he P
      (show CornerPart (K := K) (e := e) M →ₗ[he.Corner]
          CornerPart (K := K) (e := e) N from f.hom)
  map_preimage {M N} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    exact cornerPartMap_lift_apply (K := K) he P
      (show CornerPart (K := K) (e := e) M →ₗ[he.Corner]
          CornerPart (K := K) (e := e) N from f.hom) y
  preimage_map {M N} g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    exact lift_cornerPartMap_apply (K := K) he P g m

/-! ## Essential surjectivity from the finite fullness frame -/

/-- The matrix representation of an ambient element on a finite power of a
corner module. -/
def frameAction (P : FullFrame e) (Y : ModuleCat.{u} he.Corner) (r : A) :
    (Fin P.n → Y) →ₗ[K] (Fin P.n → Y) where
  toFun v i := ∑ j, frameCoeff he P i r j • v j
  map_add' v w := by
    funext i
    simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]
  map_smul' k v := by
    funext i
    simp only [Pi.smul_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact (smul_comm k (frameCoeff he P i r j) (v j)).symm

@[simp]
theorem frameAction_apply (P : FullFrame e) (Y : ModuleCat.{u} he.Corner)
    (r : A) (v : Fin P.n → Y) (i : Fin P.n) :
    frameAction (K := K) he P Y r v i =
      ∑ j, frameCoeff he P i r j • v j := rfl

/-- Matrix coefficients multiply according to multiplication in `A`. -/
theorem frameCoeff_mul_sum (P : FullFrame e) (i : Fin P.n)
    (r s : A) (k : Fin P.n) :
    ∑ j, frameCoeff he P i r j * frameCoeff he P j s k =
      frameCoeff he P i (r * s) k := by
  apply Subtype.ext
  change cornerValAddHom he
      (∑ j, frameCoeff he P i r j * frameCoeff he P j s k) =
    (frameCoeff he P i (r * s) k).1
  rw [map_sum]
  simp only [cornerValAddHom_apply, frameCoeff_val]
  change
    ∑ j, (e * P.right i * r * P.left j * e) *
        (e * P.right j * s * P.left k * e) =
      e * P.right i * (r * s) * P.left k * e
  calc
    ∑ j, (e * P.right i * r * P.left j * e) *
        (e * P.right j * s * P.left k * e) =
      (e * P.right i * r) *
        (∑ j, P.left j * e * P.right j) *
          (s * P.left k * e) := by
            rw [Finset.mul_sum, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro j _
            calc
              (e * P.right i * r * P.left j * e) *
                  (e * P.right j * s * P.left k * e) =
                (e * P.right i * r * P.left j) * (e * e) *
                  (P.right j * s * P.left k * e) := by noncomm_ring
              _ = (e * P.right i * r * P.left j) * e *
                  (P.right j * s * P.left k * e) := by rw [he.eq]
              _ = (e * P.right i * r) * (P.left j * e * P.right j) *
                  (s * P.left k * e) := by noncomm_ring
    _ = (e * P.right i * r) * (s * P.left k * e) := by
      rw [P.complete, mul_one]
    _ = e * P.right i * (r * s) * P.left k * e := by noncomm_ring

/-- The frame matrices form a multiplicative representation. -/
theorem frameAction_mul (P : FullFrame e) (Y : ModuleCat.{u} he.Corner)
    (r s : A) (v : Fin P.n → Y) :
    frameAction (K := K) he P Y r (frameAction (K := K) he P Y s v) =
      frameAction (K := K) he P Y (r * s) v := by
  funext i
  simp only [frameAction_apply]
  simp_rw [Finset.smul_sum, ← mul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.sum_smul, frameCoeff_mul_sum]

theorem frameAction_add (P : FullFrame e) (Y : ModuleCat.{u} he.Corner)
    (r s : A) (v : Fin P.n → Y) :
    frameAction (K := K) he P Y (r + s) v =
      frameAction (K := K) he P Y r v + frameAction (K := K) he P Y s v := by
  funext i
  simp only [frameAction_apply, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hc : frameCoeff he P i (r + s) j =
      frameCoeff he P i r j + frameCoeff he P i s j := by
    apply Subtype.ext
    simp only [frameCoeff_val, corner_add_val]
    noncomm_ring
  rw [hc, add_smul]

theorem frameAction_zero (P : FullFrame e) (Y : ModuleCat.{u} he.Corner)
    (v : Fin P.n → Y) :
    frameAction (K := K) he P Y 0 v = 0 := by
  funext i
  simp only [frameAction_apply, Pi.zero_apply]
  apply Finset.sum_eq_zero
  intro j _
  have hz : frameCoeff he P i 0 j = 0 := by
    apply Subtype.ext
    simp only [frameCoeff_val, corner_zero_val]
    noncomm_ring
  rw [hz]
  exact zero_smul he.Corner (v j)

/-- The fixed space of the frame matrix for `1`; this is the induced ambient
module underlying an arbitrary corner module. -/
abbrev FrameModuleCarrier (P : FullFrame e) (Y : ModuleCat.{u} he.Corner) : Type u :=
  (frameAction (K := K) he P Y 1).fixedSubmodule

/-- Ambient `A`-module structure on the fixed space of the frame unit
matrix. -/
instance frameModuleModule (P : FullFrame e) (Y : ModuleCat.{u} he.Corner) :
    Module A (FrameModuleCarrier (K := K) he P Y) where
  smul r v := ⟨frameAction (K := K) he P Y r v.1, by
    change frameAction (K := K) he P Y 1
        (frameAction (K := K) he P Y r v.1) =
      frameAction (K := K) he P Y r v.1
    rw [frameAction_mul, one_mul]⟩
  one_smul v := by
    apply Subtype.ext
    exact v.property
  mul_smul r s v := by
    apply Subtype.ext
    exact (frameAction_mul (K := K) he P Y r s v.1).symm
  zero_smul v := by
    apply Subtype.ext
    exact frameAction_zero (K := K) he P Y v.1
  add_smul r s v := by
    apply Subtype.ext
    exact frameAction_add (K := K) he P Y r s v.1
  smul_zero r := by
    apply Subtype.ext
    exact (frameAction (K := K) he P Y r).map_zero
  smul_add r v w := by
    apply Subtype.ext
    exact (frameAction (K := K) he P Y r).map_add v.1 w.1

/-- The induced ambient module attached to a corner module. -/
def frameModule (P : FullFrame e) (Y : ModuleCat.{u} he.Corner) :
    ModuleCat.{u} A :=
  ModuleCat.of A (FrameModuleCarrier (K := K) he P Y)

@[simp]
theorem frameModule_smul_val (P : FullFrame e) (Y : ModuleCat.{u} he.Corner)
    (r : A) (v : FrameModuleCarrier (K := K) he P Y) :
    ((r • v : FrameModuleCarrier (K := K) he P Y)).1 =
      frameAction (K := K) he P Y r v.1 := rfl

/-- The corner coefficient `e b_i r e` occurring when the frame action is
applied to the canonical analyzed vector. -/
def frameAnalyzeCoeff (P : FullFrame e) (i : Fin P.n) (r : A) : he.Corner :=
  ⟨e * P.right i * r * e, by
    apply (Subsemigroup.mem_corner_iff he).mpr
    constructor
    · simp only [← mul_assoc, he.eq]
    · simp only [mul_assoc, he.eq]⟩

@[simp]
theorem frameAnalyzeCoeff_val (P : FullFrame e) (i : Fin P.n) (r : A) :
    (frameAnalyzeCoeff he P i r).1 = e * P.right i * r * e := rfl

/-- Coefficient contraction against the canonical analysis column. -/
theorem frameCoeff_rightCorner_sum (P : FullFrame e) (i : Fin P.n) (r : A) :
    ∑ j, frameCoeff he P i r j * frameRightCorner he P j =
      frameAnalyzeCoeff he P i r := by
  apply Subtype.ext
  change cornerValAddHom he
      (∑ j, frameCoeff he P i r j * frameRightCorner he P j) =
    (frameAnalyzeCoeff he P i r).1
  rw [map_sum]
  simp only [cornerValAddHom_apply, frameAnalyzeCoeff_val]
  calc
    ∑ j, (e * P.right i * r * P.left j * e) *
        (e * P.right j * e) =
      (e * P.right i * r) *
        (∑ j, P.left j * e * P.right j) * e := by
          rw [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _
          calc
            (e * P.right i * r * P.left j * e) *
                (e * P.right j * e) =
              (e * P.right i * r * P.left j) * (e * e) *
                (P.right j * e) := by noncomm_ring
            _ = (e * P.right i * r * P.left j) * e *
                (P.right j * e) := by rw [he.eq]
            _ = (e * P.right i * r) * (P.left j * e * P.right j) * e := by
              noncomm_ring
    _ = e * P.right i * r * e := by rw [P.complete, mul_one]

/-- Canonical analysis column in a finite power of a corner module. -/
def thetaVector (P : FullFrame e) (Y : ModuleCat.{u} he.Corner) (y : Y) :
    Fin P.n → Y :=
  fun i ↦ frameRightCorner he P i • y

@[simp]
theorem thetaVector_apply (P : FullFrame e) (Y : ModuleCat.{u} he.Corner)
    (y : Y) (i : Fin P.n) :
    thetaVector he P Y y i = frameRightCorner he P i • y := rfl

/-- The frame action on the canonical analysis column. -/
theorem frameAction_thetaVector (P : FullFrame e) (Y : ModuleCat.{u} he.Corner)
    (r : A) (y : Y) :
    frameAction (K := K) he P Y r (thetaVector he P Y y) =
      fun i ↦ frameAnalyzeCoeff he P i r • y := by
  funext i
  simp only [frameAction_apply, thetaVector_apply, ← mul_smul]
  rw [← Finset.sum_smul, frameCoeff_rightCorner_sum]

/-- The canonical analysis column lies in the fixed space of the frame unit. -/
def thetaFrame (P : FullFrame e) (Y : ModuleCat.{u} he.Corner) (y : Y) :
    FrameModuleCarrier (K := K) he P Y :=
  ⟨thetaVector he P Y y, by
    change frameAction (K := K) he P Y 1 (thetaVector he P Y y) =
      thetaVector he P Y y
    rw [frameAction_thetaVector]
    funext i
    apply congrArg (fun c : he.Corner ↦ c • y)
    apply Subtype.ext
    simp only [frameAnalyzeCoeff_val, frameRightCorner_val]
    noncomm_ring⟩

/-- The canonical analysis column is also fixed by the ambient idempotent,
hence is an object of the corner fixed part of the induced module. -/
def thetaCorner (P : FullFrame e) (Y : ModuleCat.{u} he.Corner) (y : Y) :
    CornerPart (K := K) (e := e) (frameModule (K := K) he P Y) :=
  ⟨thetaFrame (K := K) he P Y y, by
    change e • thetaFrame (K := K) he P Y y =
      thetaFrame (K := K) he P Y y
    apply Subtype.ext
    change frameAction (K := K) he P Y e (thetaVector he P Y y) =
      thetaVector he P Y y
    rw [frameAction_thetaVector]
    funext i
    apply congrArg (fun c : he.Corner ↦ c • y)
    apply Subtype.ext
    simp only [frameAnalyzeCoeff_val, frameRightCorner_val]
    noncomm_ring [he.eq]⟩

/-- Multiplication of an analysis coefficient by a corner scalar. -/
theorem frameRightCorner_mul (P : FullFrame e) (i : Fin P.n) (c : he.Corner) :
    frameRightCorner he P i * c = frameAnalyzeCoeff he P i c.1 := by
  apply Subtype.ext
  simp only [frameAnalyzeCoeff_val]
  have hc := (Subsemigroup.mem_corner_iff he).mp c.property
  calc
    (e * P.right i * e) * c.1 = e * P.right i * (e * c.1) := by
      noncomm_ring
    _ = e * P.right i * c.1 := by rw [hc.1]
    _ = e * P.right i * (c.1 * e) :=
      congrArg (fun x : A ↦ e * P.right i * x) hc.2.symm
    _ = e * P.right i * c.1 * e := by noncomm_ring

/-- The canonical analysis map is linear over the corner. -/
def thetaLinearMap (P : FullFrame e) (Y : ModuleCat.{u} he.Corner) :
    Y →ₗ[he.Corner]
      CornerPart (K := K) (e := e) (frameModule (K := K) he P Y) where
  toFun := thetaCorner (K := K) he P Y
  map_add' y y' := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    change frameRightCorner he P i • (y + y') =
      frameRightCorner he P i • y + frameRightCorner he P i • y'
    exact smul_add _ _ _
  map_smul' c y := by
    apply Subtype.ext
    apply Subtype.ext
    change thetaVector he P Y (c • y) =
      frameAction (K := K) he P Y c.1 (thetaVector he P Y y)
    rw [frameAction_thetaVector]
    funext i
    simp only [thetaVector_apply]
    rw [← mul_smul, frameRightCorner_mul]

/-- The dual corner coefficient `e a_j e`. -/
def frameLeftCorner (P : FullFrame e) (j : Fin P.n) : he.Corner :=
  ⟨e * P.left j * e, by
    apply (Subsemigroup.mem_corner_iff he).mpr
    constructor
    · simp only [← mul_assoc, he.eq]
    · simp only [mul_assoc, he.eq]⟩

@[simp]
theorem frameLeftCorner_val (P : FullFrame e) (j : Fin P.n) :
    (frameLeftCorner he P j).1 = e * P.left j * e := rfl

/-- Explicit inverse candidate to the canonical analysis map. -/
def beta (P : FullFrame e) (Y : ModuleCat.{u} he.Corner)
    (z : CornerPart (K := K) (e := e) (frameModule (K := K) he P Y)) : Y :=
  ∑ j, frameLeftCorner he P j • z.1.1 j

/-- The contraction of the dual frame coefficients is the corner unit. -/
theorem frameLeftRight_sum (P : FullFrame e) :
    ∑ j, frameLeftCorner he P j * frameRightCorner he P j = 1 := by
  apply Subtype.ext
  change cornerValAddHom he
      (∑ j, frameLeftCorner he P j * frameRightCorner he P j) =
    (1 : he.Corner).1
  rw [map_sum]
  simp only [cornerValAddHom_apply]
  change ∑ j, (e * P.left j * e) * (e * P.right j * e) = e
  calc
    ∑ j, (e * P.left j * e) * (e * P.right j * e) =
      e * (∑ j, P.left j * e * P.right j) * e := by
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        calc
          (e * P.left j * e) * (e * P.right j * e) =
              (e * P.left j) * (e * e) * (P.right j * e) := by
                noncomm_ring
          _ = (e * P.left j) * e * (P.right j * e) := by rw [he.eq]
          _ = e * (P.left j * e * P.right j) * e := by noncomm_ring
    _ = e := by rw [P.complete, mul_one, he.eq]

/-- The inverse candidate is a left inverse to analysis. -/
theorem beta_theta (P : FullFrame e) (Y : ModuleCat.{u} he.Corner) (y : Y) :
    beta (K := K) he P Y (thetaLinearMap (K := K) he P Y y) = y := by
  change ∑ j, frameLeftCorner he P j •
      (frameRightCorner he P j • y) = y
  simp only [← mul_smul]
  rw [← Finset.sum_smul, frameLeftRight_sum, one_smul]

/-- The products of analysis and dual coefficients are the matrix
coefficients for the ambient idempotent. -/
theorem frameRightLeft_mul (P : FullFrame e) (i j : Fin P.n) :
    frameRightCorner he P i * frameLeftCorner he P j =
      frameCoeff he P i e j := by
  apply Subtype.ext
  simp only [frameCoeff_val]
  calc
    (e * P.right i * e) * (e * P.left j * e) =
        (e * P.right i) * (e * e) * (P.left j * e) := by noncomm_ring
    _ = (e * P.right i) * e * (P.left j * e) := by rw [he.eq]
    _ = e * P.right i * e * P.left j * e := by noncomm_ring

/-- The inverse candidate is also a right inverse on the `e`-fixed part. -/
theorem theta_beta (P : FullFrame e) (Y : ModuleCat.{u} he.Corner)
    (z : CornerPart (K := K) (e := e) (frameModule (K := K) he P Y)) :
    thetaLinearMap (K := K) he P Y (beta (K := K) he P Y z) = z := by
  apply Subtype.ext
  apply Subtype.ext
  funext i
  change frameRightCorner he P i •
      (∑ j, frameLeftCorner he P j • z.1.1 j) = z.1.1 i
  rw [Finset.smul_sum]
  simp_rw [← mul_smul, frameRightLeft_mul]
  have hz := z.property
  change e • z.1 = z.1 at hz
  have hzv := congrArg Subtype.val hz
  change frameAction (K := K) he P Y e z.1.1 = z.1.1 at hzv
  exact congrFun hzv i

/-- Linear equivalence between an arbitrary corner module and the corner
fixed part of its induced ambient frame module. -/
def thetaLinearEquiv (P : FullFrame e) (Y : ModuleCat.{u} he.Corner) :
    Y ≃ₗ[he.Corner]
      CornerPart (K := K) (e := e) (frameModule (K := K) he P Y) :=
  LinearEquiv.ofBijective (thetaLinearMap (K := K) he P Y) ⟨
    (fun y y' h ↦ by
      rw [← beta_theta (K := K) he P Y y,
        ← beta_theta (K := K) he P Y y', h]),
    (fun z ↦ ⟨beta (K := K) he P Y z, theta_beta (K := K) he P Y z⟩)⟩

/-- Essential surjectivity of the corner functor. -/
theorem cornerFunctor_essSurj (P : FullFrame e) :
    (cornerFunctor (K := K) he).EssSurj := by
  refine ⟨fun Y ↦ ?_⟩
  refine ⟨frameModule (K := K) he P Y, ⟨?_⟩⟩
  exact (thetaLinearEquiv (K := K) he P Y).symm.toModuleIso

/-- The categorical equivalence induced by a chosen full frame. -/
def cornerEquivalence (P : FullFrame e) :
    ModuleCat.{u} A ≌ ModuleCat.{u} he.Corner := by
  let hff := cornerFunctorFullyFaithful (K := K) he P
  letI : (cornerFunctor (K := K) he).Faithful := hff.faithful
  letI : (cornerFunctor (K := K) he).Full := hff.full
  letI : (cornerFunctor (K := K) he).EssSurj :=
    cornerFunctor_essSurj (K := K) he P
  letI : (cornerFunctor (K := K) he).IsEquivalence :=
    { faithful := inferInstance
      full := inferInstance
      essSurj := inferInstance }
  exact (cornerFunctor (K := K) he).asEquivalence

/-- The corner fixed-space functor is `K`-linear. -/
theorem cornerFunctorLinear : (cornerFunctor (K := K) he).Linear K where
  map_smul {M N} f k := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    have hy := (cornerPartMap (K := K) he f y).property
    change e • f.hom y.1 = f.hom y.1 at hy
    change (algebraMap K A k) • f.hom y.1 =
      (algebraMap K A k * e) • f.hom y.1
    rw [mul_smul, hy]

/-- Full-frame form of full-idempotent Morita equivalence. -/
def moritaEquivalenceOfFrame (P : FullFrame e) :
    MoritaEquivalence K A he.Corner where
  eqv := cornerEquivalence (K := K) he P
  linear := cornerFunctorLinear (K := K) he

/-- A full idempotent induces a `K`-linear Morita equivalence with its
corner. -/
theorem fullIdempotentMorita (hfull : IsFullElem e) :
    Nonempty (MoritaEquivalence K A he.Corner) :=
  ⟨moritaEquivalenceOfFrame (K := K) he (FullFrame.ofFull hfull)⟩

/-- Discharge of the exact project-level full-idempotent Morita bridge. -/
theorem fullIdempotentMoritaBridge :
    FullIdempotentMoritaBridge (K := K) (A := A) := by
  intro e he hfull
  letI : Algebra K he.Corner := cornerAlgebra (K := K) he
  exact fullIdempotentMorita (K := K) he hfull

/-- Unconditional paper-facing finite-dimensional Morita basicization over an
algebraically closed field. -/
theorem finiteDimensionalMoritaBasicization
    (K : Type u) [Field K] [IsAlgClosed K] :
    FiniteDimensionalMoritaBasicization K :=
  finiteDimensionalMoritaBasicization_of_fullIdempotentMoritaBridge K
    (fun A => fullIdempotentMoritaBridge (K := K) (A := A))

end QuotientSubmoduleEquidistribution.FullIdempotentMorita
