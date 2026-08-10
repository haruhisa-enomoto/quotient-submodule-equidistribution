import OpConjecture.RepresentationTheory.FullIdempotentMorita

/-!
# Block connectedness of full idempotent corners

For a full idempotent `e`, a central corner element `z ∈ eAe` has the
standard lift `∑ aᵢ z bᵢ`, where `∑ aᵢ e bᵢ = 1`.  The lift is
central and compression by `e` recovers `z`.  This gives the portion of
Morita invariance of centers needed to show that a full corner of a
block-connected algebra is block connected.
-/

noncomputable section

namespace OpConjecture.FullIdempotentMorita

universe u

variable {A : Type u} [Ring A]
  {e : A} (he : IsIdempotentElem e)

/-- The standard lift of a corner element along a chosen fullness frame. -/
def liftCornerElement (P : FullFrame e) (z : he.Corner) : A :=
  ∑ i, P.left i * z.1 * P.right i

@[simp]
theorem liftCornerElement_zero (P : FullFrame e) :
    liftCornerElement he P 0 = 0 := by
  simp [liftCornerElement]

@[simp]
theorem liftCornerElement_add (P : FullFrame e) (z w : he.Corner) :
    liftCornerElement he P (z + w) =
      liftCornerElement he P z + liftCornerElement he P w := by
  simp only [liftCornerElement, corner_add_val, mul_add, add_mul,
    Finset.sum_add_distrib]

/-- A central corner element has a central lift to the ambient ring. -/
theorem liftCornerElement_isMulCentral
    (P : FullFrame e) (z : he.Corner) (hz : IsMulCentral z) :
    IsMulCentral (liftCornerElement he P z) := by
  have hzCorner := (Subsemigroup.mem_corner_iff he).mp z.property
  refine ⟨?_, fun _ _ ↦ (mul_assoc _ _ _).symm,
    fun _ _ ↦ mul_assoc _ _ _⟩
  intro r
  rw [commute_iff_eq]
  unfold liftCornerElement
  calc
    (∑ i, P.left i * z.1 * P.right i) * r =
        ∑ i, P.left i * z.1 * P.right i * r := by
      rw [Finset.sum_mul]
    _ = ∑ i, ∑ j,
        P.left i * z.1 *
          (e * P.right i * r * P.left j * e) * P.right j := by
      apply Finset.sum_congr rfl
      intro i _
      calc
        P.left i * z.1 * P.right i * r =
            (P.left i * z.1 * P.right i * r) * 1 := by rw [mul_one]
        _ = (P.left i * z.1 * P.right i * r) *
            (∑ j, P.left j * e * P.right j) := by rw [P.complete]
        _ = ∑ j,
            (P.left i * z.1 * P.right i * r) *
              (P.left j * e * P.right j) := by rw [Finset.mul_sum]
        _ = ∑ j, P.left i * z.1 *
            (e * P.right i * r * P.left j * e) * P.right j := by
          apply Finset.sum_congr rfl
          intro j _
          calc
            (P.left i * z.1 * P.right i * r) *
                (P.left j * e * P.right j) =
                (P.left i * (z.1 * e) * P.right i * r) *
                  (P.left j * e * P.right j) := by
              rw [hzCorner.2]
            _ = P.left i * z.1 *
                (e * P.right i * r * P.left j * e) * P.right j := by
              simp only [mul_assoc]
    _ = ∑ i, ∑ j,
        P.left i * (e * P.right i * r * P.left j * e) *
          z.1 * P.right j := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      let c : he.Corner :=
        ⟨e * P.right i * r * P.left j * e, by
          exact ⟨P.right i * r * P.left j, by simp only [mul_assoc]⟩⟩
      have hcomm :
          z.1 * (e * P.right i * r * P.left j * e) =
            (e * P.right i * r * P.left j * e) * z.1 :=
        congrArg Subtype.val (hz.comm c).eq
      calc
        P.left i * z.1 *
            (e * P.right i * r * P.left j * e) * P.right j =
            P.left i *
              (z.1 * (e * P.right i * r * P.left j * e)) *
                P.right j := by simp only [mul_assoc]
        _ = P.left i *
              ((e * P.right i * r * P.left j * e) * z.1) *
                P.right j := by rw [hcomm]
        _ = P.left i * (e * P.right i * r * P.left j * e) *
              z.1 * P.right j := by simp only [mul_assoc]
    _ = ∑ j, ∑ i,
        P.left i * (e * P.right i * r * P.left j * e) *
          z.1 * P.right j := by rw [Finset.sum_comm]
    _ = ∑ j, r * P.left j * z.1 * P.right j := by
      apply Finset.sum_congr rfl
      intro j _
      calc
        ∑ i, P.left i *
            (e * P.right i * r * P.left j * e) * z.1 * P.right j =
            ∑ i, (P.left i * e * P.right i) *
              (r * P.left j * e * z.1 * P.right j) := by
          apply Finset.sum_congr rfl
          intro i _
          noncomm_ring
        _ = (∑ i, P.left i * e * P.right i) *
            (r * P.left j * e * z.1 * P.right j) := by
          rw [Finset.sum_mul]
        _ = r * P.left j * z.1 * P.right j := by
          rw [P.complete, one_mul]
          calc
            r * P.left j * e * z.1 * P.right j =
                r * P.left j * (e * z.1) * P.right j := by
              simp only [mul_assoc]
            _ = r * P.left j * z.1 * P.right j := by
              rw [hzCorner.1]
    _ = r * (∑ j, P.left j * z.1 * P.right j) := by
      rw [Finset.mul_sum]
      simp only [mul_assoc]

/-- Compression of the central lift by the full idempotent recovers the
original corner element. -/
theorem compress_liftCornerElement
    (P : FullFrame e) (z : he.Corner) (hz : IsMulCentral z) :
    e * liftCornerElement he P z * e = z.1 := by
  have hzCorner := (Subsemigroup.mem_corner_iff he).mp z.property
  unfold liftCornerElement
  rw [Finset.mul_sum, Finset.sum_mul]
  calc
    ∑ i, e * (P.left i * z.1 * P.right i) * e =
        ∑ i, z.1 * (e * P.left i * e * P.right i * e) := by
      apply Finset.sum_congr rfl
      intro i _
      let c : he.Corner :=
        ⟨e * P.left i * e, by
          exact ⟨P.left i, rfl⟩⟩
      have hcomm :
          z.1 * (e * P.left i * e) =
            (e * P.left i * e) * z.1 :=
        congrArg Subtype.val (hz.comm c).eq
      calc
        e * (P.left i * z.1 * P.right i) * e =
            e * P.left i * (e * z.1) * P.right i * e := by
          rw [hzCorner.1]
          simp only [mul_assoc]
        _ = (e * P.left i * e) * z.1 * P.right i * e := by
          simp only [mul_assoc]
        _ = z.1 * (e * P.left i * e) * P.right i * e := by
          rw [← hcomm]
        _ = z.1 * (e * P.left i * e * P.right i * e) := by
          simp only [mul_assoc]
    _ = z.1 * (∑ i, e * P.left i * e * P.right i * e) := by
      rw [Finset.mul_sum]
    _ = z.1 * (e * (∑ i, P.left i * e * P.right i) * e) := by
      congr 1
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      noncomm_ring
    _ = z.1 := by rw [P.complete, mul_one, he.eq, hzCorner.2]

/-- A central ambient element is determined by its compression to a full
corner. -/
theorem eq_zero_of_isMulCentral_of_compress_eq_zero
    (he : IsIdempotentElem e)
    (P : FullFrame e) (c : A) (hc : IsMulCentral c)
    (hcompress : e * c * e = 0) :
    c = 0 := by
  have hec : e * c = e * c * e := by
    calc
      e * c = (e * e) * c := by rw [he.eq]
      _ = e * (e * c) := by rw [mul_assoc]
      _ = e * (c * e) := by rw [(hc.comm e).eq]
      _ = e * c * e := by rw [mul_assoc]
  calc
    c = 1 * c := (one_mul c).symm
    _ = (∑ i, P.left i * e * P.right i) * c := by rw [P.complete]
    _ = ∑ i, (P.left i * e * P.right i) * c := by
      rw [Finset.sum_mul]
    _ = ∑ _i : Fin P.n, 0 := by
      apply Finset.sum_congr rfl
      intro i _
      calc
        (P.left i * e * P.right i) * c =
            P.left i * e * (P.right i * c) := by
          simp only [mul_assoc]
        _ = P.left i * e * (c * P.right i) := by
          rw [(hc.comm (P.right i)).eq]
        _ = P.left i * (e * c) * P.right i := by
          simp only [mul_assoc]
        _ = P.left i * (e * c * e) * P.right i :=
          congrArg (fun x : A ↦ P.left i * x * P.right i) hec
        _ = 0 := by rw [hcompress]; simp
    _ = 0 := by simp

/-- The lift of a central idempotent of a full corner is a central
idempotent of the ambient ring. -/
theorem liftCornerElement_isIdempotentElem
    (P : FullFrame e) (z : he.Corner)
    (hzCentral : IsMulCentral z) (hzIdem : IsIdempotentElem z) :
    IsIdempotentElem (liftCornerElement he P z) := by
  let L := liftCornerElement he P z
  have hLCentral : IsMulCentral L :=
    liftCornerElement_isMulCentral he P z hzCentral
  have hcompress : e * L * e = z.1 :=
    compress_liftCornerElement he P z hzCentral
  have hcommE : L * e = e * L := (hLCentral.comm e).eq
  have hcompressSq : e * (L * L) * e = z.1 * z.1 := by
    calc
      e * (L * L) * e = (e * L * e) * (e * L * e) := by
        symm
        calc
          (e * L * e) * (e * L * e) = e * L * (e * L) * e := by
            calc
              (e * L * e) * (e * L * e) =
                  e * L * (e * e) * L * e := by noncomm_ring
              _ = e * L * e * L * e := by rw [he.eq]
              _ = e * L * (e * L) * e := by
                simp only [mul_assoc]
          _ = e * L * (L * e) * e := by rw [hcommE]
          _ = e * (L * L) * e := by
            calc
              e * L * (L * e) * e = e * (L * L) * (e * e) := by
                noncomm_ring
              _ = e * (L * L) * e := by rw [he.eq]
      _ = z.1 * z.1 := by rw [hcompress]
  let Lc : Subring.center A := ⟨L, hLCentral⟩
  let delta : Subring.center A := Lc * Lc - Lc
  have hDeltaCentral : IsMulCentral (L * L - L) := by
    exact delta.property
  have hDeltaCompress : e * (L * L - L) * e = 0 := by
    calc
      e * (L * L - L) * e =
          e * (L * L) * e - e * L * e := by noncomm_ring
      _ = z.1 * z.1 - z.1 := by rw [hcompressSq, hcompress]
      _ = 0 := by
        have hzVal := congrArg Subtype.val hzIdem.eq
        change z.1 * z.1 = z.1 at hzVal
        exact sub_eq_zero.mpr hzVal
  have hDeltaZero : L * L - L = 0 :=
    eq_zero_of_isMulCentral_of_compress_eq_zero
      he P (L * L - L) hDeltaCentral hDeltaCompress
  exact sub_eq_zero.mp hDeltaZero

/-- A full idempotent corner of a block-connected ring is block connected. -/
theorem fullCorner_isBlockConnected
    (P : FullFrame e)
    (hConnected : ∀ z : A, IsIdempotentElem z → IsMulCentral z →
      z = 0 ∨ z = 1) :
    ∀ z : he.Corner, IsIdempotentElem z → IsMulCentral z →
      z = 0 ∨ z = 1 := by
  intro z hzIdem hzCentral
  let L := liftCornerElement he P z
  have hLCentral : IsMulCentral L :=
    liftCornerElement_isMulCentral he P z hzCentral
  have hLIdem : IsIdempotentElem L :=
    liftCornerElement_isIdempotentElem he P z hzCentral hzIdem
  have hcompress : e * L * e = z.1 :=
    compress_liftCornerElement he P z hzCentral
  rcases hConnected L hLIdem hLCentral with hzero | hone
  · left
    rw [hzero] at hcompress
    refine Subtype.ext (a1 := z) (a2 := (0 : he.Corner)) ?_
    change z.1 = 0
    calc
      z.1 = e * 0 * e := hcompress.symm
      _ = 0 := by simp
  · right
    rw [hone] at hcompress
    refine Subtype.ext (a1 := z) (a2 := (1 : he.Corner)) ?_
    change z.1 = e
    calc
      z.1 = e * 1 * e := hcompress.symm
      _ = e := by rw [mul_one, he.eq]

end OpConjecture.FullIdempotentMorita
