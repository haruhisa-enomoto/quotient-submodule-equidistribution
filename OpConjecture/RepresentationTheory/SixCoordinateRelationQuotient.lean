import OpConjecture.RepresentationTheory.PeirceCotangentSpanning
import OpConjecture.RepresentationTheory.SixCoordinateQuotientConstructor
import OpConjecture.RepresentationTheory.SingleCrossTriangularEquivalence

/-!
# The loop--two-cycle relation quotient has the six-coordinate basis

This file closes the algebraic gap between the Peirce/cotangent reduction and
the six-coordinate representation-infinite family.  Cotangent spanning gives
the six named quotient classes spanning, the filtered detector argument gives
their linear independence, and the defining relation ideal gives the complete
finite multiplication table.
-/

noncomputable section

namespace OpConjecture.QuotientSurvival.TwoCoordinateData

open OpConjecture.CotangentExtBridge
open OpConjecture.LoopTwoCycleFamily

universe u v

variable {K B : Type u}
  [Field K] [Ring B] [Algebra K B] [IsArtinianRing B]
  (D : TwoCoordinateData (K := K) (B := B))

private abbrev relationIdeal (x a b : B) : Ideal B :=
  loopTwoCycleRelationIdeal x a b

omit [IsArtinianRing B] in
private theorem jacobsonCube_le_relationIdeal (x a b : B) :
    (Ring.jacobson B) ^ 3 ≤ relationIdeal x a b := by
  intro z hz
  change z ∈
    (TwoSidedIdeal.span (loopTwoCycleRelationSet x a b)).asIdeal
  exact TwoSidedIdeal.subset_span (Or.inl hz)

omit [IsArtinianRing B] in
private theorem relationGenerator_mem
    (x a b z : B) (hz : z ∈ loopTwoCycleRelationSet x a b) :
    z ∈ relationIdeal x a b := by
  change z ∈
    (TwoSidedIdeal.span (loopTwoCycleRelationSet x a b)).asIdeal
  exact TwoSidedIdeal.subset_span hz

private theorem x_mul_a_eq_zero
    {x a : B}
    (hxright : x * D.liftedCoordinate 0 = x)
    (haleft : D.liftedCoordinate 1 * a = a) :
    x * a = 0 := by
  calc
    x * a = (x * D.liftedCoordinate 0) *
        (D.liftedCoordinate 1 * a) := by rw [hxright, haleft]
    _ = x * (D.liftedCoordinate 0 * D.liftedCoordinate 1) * a := by
      noncomm_ring
    _ = 0 := by
      rw [D.liftedCoordinate_complete.ortho (by decide : (0 : Fin 2) ≠ 1)]
      simp

private theorem a_mul_a_eq_zero
    {a : B}
    (haright : a * D.liftedCoordinate 0 = a)
    (haleft : D.liftedCoordinate 1 * a = a) :
    a * a = 0 := by
  calc
    a * a = (a * D.liftedCoordinate 0) *
        (D.liftedCoordinate 1 * a) := by rw [haright, haleft]
    _ = a * (D.liftedCoordinate 0 * D.liftedCoordinate 1) * a := by
      noncomm_ring
    _ = 0 := by
      rw [D.liftedCoordinate_complete.ortho (by decide : (0 : Fin 2) ≠ 1)]
      simp

private theorem b_mul_x_eq_zero
    {x b : B}
    (hbright : b * D.liftedCoordinate 1 = b)
    (hxleft : D.liftedCoordinate 0 * x = x) :
    b * x = 0 := by
  calc
    b * x = (b * D.liftedCoordinate 1) *
        (D.liftedCoordinate 0 * x) := by rw [hbright, hxleft]
    _ = b * (D.liftedCoordinate 1 * D.liftedCoordinate 0) * x := by
      noncomm_ring
    _ = 0 := by
      rw [D.liftedCoordinate_complete.ortho (by decide : (1 : Fin 2) ≠ 0)]
      simp

private theorem b_mul_b_eq_zero
    {b : B}
    (hbright : b * D.liftedCoordinate 1 = b)
    (hbleft : D.liftedCoordinate 0 * b = b) :
    b * b = 0 := by
  calc
    b * b = (b * D.liftedCoordinate 1) *
        (D.liftedCoordinate 0 * b) := by rw [hbright, hbleft]
    _ = b * (D.liftedCoordinate 1 * D.liftedCoordinate 0) * b := by
      noncomm_ring
    _ = 0 := by
      rw [D.liftedCoordinate_complete.ortho (by decide : (1 : Fin 2) ≠ 0)]
      simp

private theorem radicalProduct_mod_relationIdeal
    {x a b p q : B}
    (hxJ : x ∈ Ring.jacobson B)
    (haJ : a ∈ Ring.jacobson B)
    (hbJ : b ∈ Ring.jacobson B)
    (hxleft : D.liftedCoordinate 0 * x = x)
    (hxright : x * D.liftedCoordinate 0 = x)
    (haleft : D.liftedCoordinate 1 * a = a)
    (haright : a * D.liftedCoordinate 0 = a)
    (hbleft : D.liftedCoordinate 0 * b = b)
    (hbright : b * D.liftedCoordinate 1 = b)
    (hspan : JacobsonCotangentSpannedBy (K := K) x a b)
    (hp : p ∈ Ring.jacobson B) (hq : q ∈ Ring.jacobson B) :
    ∃ c : K,
      Ideal.Quotient.mk (relationIdeal x a b) (p * q) =
        c • Ideal.Quotient.mk (relationIdeal x a b) (b * a) := by
  obtain ⟨px, pa, pb, hp2⟩ := hspan p hp
  obtain ⟨qx, qa, qb, hq2⟩ := hspan q hq
  let p₁ : B := px • x + pa • a + pb • b
  let q₁ : B := qx • x + qa • a + qb • b
  have hpEq : p = p₁ + (p - p₁) := by abel
  have hqEq : q = q₁ + (q - q₁) := by abel
  have hp₁J : p₁ ∈ Ring.jacobson B := by
    exact (Ring.jacobson B).add_mem
      ((Ring.jacobson B).add_mem
        (((Ring.jacobson B : Submodule B B).restrictScalars K).smul_mem px hxJ)
        (((Ring.jacobson B : Submodule B B).restrictScalars K).smul_mem pa haJ))
      (((Ring.jacobson B : Submodule B B).restrictScalars K).smul_mem pb hbJ)
  have hq₁J : q₁ ∈ Ring.jacobson B := by
    exact (Ring.jacobson B).add_mem
      ((Ring.jacobson B).add_mem
        (((Ring.jacobson B : Submodule B B).restrictScalars K).smul_mem qx hxJ)
        (((Ring.jacobson B : Submodule B B).restrictScalars K).smul_mem qa haJ))
      (((Ring.jacobson B : Submodule B B).restrictScalars K).smul_mem qb hbJ)
  have herror :
      p * q - p₁ * q₁ ∈ (Ring.jacobson B) ^ 3 := by
    rw [hpEq, hqEq]
    have hleft : (p - p₁) * q₁ ∈ (Ring.jacobson B) ^ 3 := by
      rw [show (3 : ℕ) = 2 + 1 by omega, Ideal.IsTwoSided.pow_add,
        Submodule.pow_one]
      exact Ideal.mul_mem_mul hp2 hq₁J
    have hright : p₁ * (q - q₁) ∈ (Ring.jacobson B) ^ 3 := by
      rw [show (3 : ℕ) = 1 + 2 by omega, Ideal.IsTwoSided.pow_add,
        Submodule.pow_one]
      exact Ideal.mul_mem_mul hp₁J hq2
    have hboth : (p - p₁) * (q - q₁) ∈ (Ring.jacobson B) ^ 3 := by
      have h4 : (p - p₁) * (q - q₁) ∈ (Ring.jacobson B) ^ 4 := by
        rw [show (4 : ℕ) = 2 + 2 by omega, Ideal.IsTwoSided.pow_add]
        exact Ideal.mul_mem_mul hp2 hq2
      exact Ideal.pow_le_pow_right (by omega : 3 ≤ 4) h4
    convert ((Ring.jacobson B) ^ 3).add_mem
      (((Ring.jacobson B) ^ 3).add_mem hleft hright) hboth using 1
    noncomm_ring
  have hsource :
      p₁ * q₁ - (pb * qa) • (b * a) ∈ relationIdeal x a b := by
    have hxx : x * x ∈ relationIdeal x a b :=
      relationGenerator_mem x a b (x * x) (by simp [loopTwoCycleRelationSet])
    have hax : a * x ∈ relationIdeal x a b :=
      relationGenerator_mem x a b (a * x) (by simp [loopTwoCycleRelationSet])
    have hxb : x * b ∈ relationIdeal x a b :=
      relationGenerator_mem x a b (x * b) (by simp [loopTwoCycleRelationSet])
    have hab : a * b ∈ relationIdeal x a b :=
      relationGenerator_mem x a b (a * b) (by simp [loopTwoCycleRelationSet])
    have hxa : x * a = 0 := D.x_mul_a_eq_zero hxright haleft
    have haa : a * a = 0 := D.a_mul_a_eq_zero haright haleft
    have hbx : b * x = 0 := D.b_mul_x_eq_zero hbright hxleft
    have hbb : b * b = 0 := D.b_mul_b_eq_zero hbright hbleft
    dsimp [p₁, q₁]
    simp only [mul_add, add_mul, smul_mul_smul_comm, hxa, haa, hbx, hbb,
      smul_zero, zero_add, add_zero]
    have hxx' : (px * qx) • (x * x) ∈ relationIdeal x a b :=
      ((relationIdeal x a b : Submodule B B).restrictScalars K).smul_mem _ hxx
    have hax' : (pa * qx) • (a * x) ∈ relationIdeal x a b :=
      ((relationIdeal x a b : Submodule B B).restrictScalars K).smul_mem _ hax
    have hxb' : (px * qb) • (x * b) ∈ relationIdeal x a b :=
      ((relationIdeal x a b : Submodule B B).restrictScalars K).smul_mem _ hxb
    have hab' : (pa * qb) • (a * b) ∈ relationIdeal x a b :=
      ((relationIdeal x a b : Submodule B B).restrictScalars K).smul_mem _ hab
    convert (relationIdeal x a b).add_mem hxx'
      ((relationIdeal x a b).add_mem hax'
        ((relationIdeal x a b).add_mem hxb' hab')) using 1
    · abel
  refine ⟨pb * qa, ?_⟩
  apply Ideal.Quotient.eq.mpr
  change p * q - (pb * qa) • (b * a) ∈ relationIdeal x a b
  have herrorH := jacobsonCube_le_relationIdeal x a b herror
  convert (relationIdeal x a b).add_mem herrorH hsource using 1
  · noncomm_ring

private theorem jacobsonSquare_mod_relationIdeal
    {x a b z : B}
    (hxJ : x ∈ Ring.jacobson B)
    (haJ : a ∈ Ring.jacobson B)
    (hbJ : b ∈ Ring.jacobson B)
    (hxleft : D.liftedCoordinate 0 * x = x)
    (hxright : x * D.liftedCoordinate 0 = x)
    (haleft : D.liftedCoordinate 1 * a = a)
    (haright : a * D.liftedCoordinate 0 = a)
    (hbleft : D.liftedCoordinate 0 * b = b)
    (hbright : b * D.liftedCoordinate 1 = b)
    (hspan : JacobsonCotangentSpannedBy (K := K) x a b)
    (hz : z ∈ (Ring.jacobson B) ^ 2) :
    ∃ c : K,
      Ideal.Quotient.mk (relationIdeal x a b) z =
        c • Ideal.Quotient.mk (relationIdeal x a b) (b * a) := by
  rw [show (2 : ℕ) = 1 + 1 by omega, Ideal.IsTwoSided.pow_add,
    Submodule.pow_one] at hz
  refine Submodule.mul_induction_on hz ?_ ?_
  · intro p hp q hq
    exact D.radicalProduct_mod_relationIdeal hxJ haJ hbJ
      hxleft hxright haleft haright hbleft hbright hspan hp hq
  · intro z w hz hw
    obtain ⟨cz, hcz⟩ := hz
    obtain ⟨cw, hcw⟩ := hw
    refine ⟨cz + cw, ?_⟩
    rw [map_add, hcz, hcw, add_smul]

/-- Cotangent spanning gives a complete six-term normal form in the
loop--two-cycle relation quotient. -/
theorem six_relationQuotientClasses_span_of_cotangentSpanned
    {x a b : B}
    (hxJ : x ∈ Ring.jacobson B)
    (haJ : a ∈ Ring.jacobson B)
    (hbJ : b ∈ Ring.jacobson B)
    (hxleft : D.liftedCoordinate 0 * x = x)
    (hxright : x * D.liftedCoordinate 0 = x)
    (haleft : D.liftedCoordinate 1 * a = a)
    (haright : a * D.liftedCoordinate 0 = a)
    (hbleft : D.liftedCoordinate 0 * b = b)
    (hbright : b * D.liftedCoordinate 1 = b)
    (hspan : JacobsonCotangentSpannedBy (K := K) x a b) :
    ⊤ ≤ Submodule.span K
      (Set.range fun i ↦
        Ideal.Quotient.mk (relationIdeal x a b)
          (D.sixPeirceElements x a b i)) := by
  intro z _
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
  let c₀ := CoordinateData.coordinateCharacter D 0 r
  let c₁ := CoordinateData.coordinateCharacter D 1 r
  let y := r - (c₀ • D.liftedCoordinate 0 + c₁ • D.liftedCoordinate 1)
  have hyJ : y ∈ Ring.jacobson B := by
    simpa [y, c₀, c₁, Fin.sum_univ_two] using
      D.diagonalRemainder_mem_jacobson r
  obtain ⟨cx, ca, cb, hy2⟩ := hspan y hyJ
  let y₂ := y - (cx • x + ca • a + cb • b)
  obtain ⟨cab, hcab⟩ :=
    D.jacobsonSquare_mod_relationIdeal hxJ haJ hbJ
      hxleft hxright haleft haright hbleft hbright hspan hy2
  rw [Submodule.mem_span_range_iff_exists_fun K]
  let coeff : SixBasisIndex → K
    | .e₁ => c₀
    | .e₂ => c₁
    | .x => cx
    | .a => ca
    | .b => cb
    | .ab => cab
  refine ⟨coeff, ?_⟩
  rw [sum_sixBasisIndex]
  simp only [sixPeirceElements]
  rw [← hcab]
  change
    Ideal.Quotient.mk (relationIdeal x a b)
        (c₀ • D.liftedCoordinate 0 + c₁ • D.liftedCoordinate 1 +
          cx • x + ca • a + cb • b + y₂) =
      Ideal.Quotient.mk (relationIdeal x a b) r
  congr 1
  dsimp [y₂, y]
  abel

omit [IsArtinianRing B] in
private theorem triple_mem_jacobsonCube
    {r s t : B}
    (hr : r ∈ Ring.jacobson B)
    (hs : s ∈ Ring.jacobson B)
    (ht : t ∈ Ring.jacobson B) :
    r * s * t ∈ (Ring.jacobson B) ^ 3 := by
  rw [show (3 : ℕ) = 2 + 1 by omega, Ideal.IsTwoSided.pow_add,
    Submodule.pow_one]
  exact Ideal.mul_mem_mul
    (by
      rw [show (2 : ℕ) = 1 + 1 by omega, Ideal.IsTwoSided.pow_add,
        Submodule.pow_one]
      exact Ideal.mul_mem_mul hr hs)
    ht

/-- The six quotient classes satisfy exactly the finite multiplication table
used by `SixDimensionalQuotientData`. -/
theorem six_relationQuotientClasses_mul
    {x a b : B}
    (hxJ : x ∈ Ring.jacobson B)
    (haJ : a ∈ Ring.jacobson B)
    (hbJ : b ∈ Ring.jacobson B)
    (hxleft : D.liftedCoordinate 0 * x = x)
    (hxright : x * D.liftedCoordinate 0 = x)
    (haleft : D.liftedCoordinate 1 * a = a)
    (haright : a * D.liftedCoordinate 0 = a)
    (hbleft : D.liftedCoordinate 0 * b = b)
    (hbright : b * D.liftedCoordinate 1 = b) :
    let H := relationIdeal x a b
    let v : SixBasisIndex → B ⧸ H := fun i ↦
      Ideal.Quotient.mk H (D.sixPeirceElements x a b i)
    ∀ i j, v i * v j = SixCoordinateBasisQuotientData.basisProduct v i j := by
  let H := relationIdeal x a b
  let q : B →ₐ[K] B ⧸ H := Ideal.Quotient.mkₐ K H
  let e₀ := D.liftedCoordinate 0
  let e₁ := D.liftedCoordinate 1
  have he₀e₀ : e₀ * e₀ = e₀ := D.liftedCoordinate_complete.idem 0
  have he₁e₁ : e₁ * e₁ = e₁ := D.liftedCoordinate_complete.idem 1
  have he₀e₁ : e₀ * e₁ = 0 :=
    D.liftedCoordinate_complete.ortho (by decide : (0 : Fin 2) ≠ 1)
  have he₁e₀ : e₁ * e₀ = 0 :=
    D.liftedCoordinate_complete.ortho (by decide : (1 : Fin 2) ≠ 0)
  have he₁x : e₁ * x = 0 := by
    calc
      e₁ * x = e₁ * (e₀ * x) := by rw [hxleft]
      _ = (e₁ * e₀) * x := by rw [mul_assoc]
      _ = 0 := by rw [he₁e₀, zero_mul]
  have hxe₁ : x * e₁ = 0 := by
    calc
      x * e₁ = (x * e₀) * e₁ := by rw [hxright]
      _ = x * (e₀ * e₁) := by rw [mul_assoc]
      _ = 0 := by rw [he₀e₁, mul_zero]
  have he₀a : e₀ * a = 0 := by
    calc
      e₀ * a = e₀ * (e₁ * a) := by rw [haleft]
      _ = (e₀ * e₁) * a := by rw [mul_assoc]
      _ = 0 := by rw [he₀e₁, zero_mul]
  have hae₁ : a * e₁ = 0 := by
    calc
      a * e₁ = (a * e₀) * e₁ := by rw [haright]
      _ = a * (e₀ * e₁) := by rw [mul_assoc]
      _ = 0 := by rw [he₀e₁, mul_zero]
  have he₁b : e₁ * b = 0 := by
    calc
      e₁ * b = e₁ * (e₀ * b) := by rw [hbleft]
      _ = (e₁ * e₀) * b := by rw [mul_assoc]
      _ = 0 := by rw [he₁e₀, zero_mul]
  have hbe₀ : b * e₀ = 0 := by
    calc
      b * e₀ = (b * e₁) * e₀ := by rw [hbright]
      _ = b * (e₁ * e₀) := by rw [mul_assoc]
      _ = 0 := by rw [he₁e₀, mul_zero]
  have he₀ba : e₀ * (b * a) = b * a := by rw [← mul_assoc, hbleft]
  have hbae₀ : (b * a) * e₀ = b * a := by rw [mul_assoc, haright]
  have he₁ba : e₁ * (b * a) = 0 := by rw [← mul_assoc, he₁b, zero_mul]
  have hbae₁ : (b * a) * e₁ = 0 := by rw [mul_assoc, hae₁, mul_zero]
  have hxa : x * a = 0 := D.x_mul_a_eq_zero hxright haleft
  have haa : a * a = 0 := D.a_mul_a_eq_zero haright haleft
  have hbx : b * x = 0 := D.b_mul_x_eq_zero hbright hxleft
  have hbb : b * b = 0 := D.b_mul_b_eq_zero hbright hbleft
  have hmkZero (z : B) (hz : z ∈ H) : q z = 0 := by
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hz
  have hxx : q (x * x) = 0 := hmkZero _ <|
    relationGenerator_mem x a b (x * x) (by simp [loopTwoCycleRelationSet])
  have hax : q (a * x) = 0 := hmkZero _ <|
    relationGenerator_mem x a b (a * x) (by simp [loopTwoCycleRelationSet])
  have hxb : q (x * b) = 0 := hmkZero _ <|
    relationGenerator_mem x a b (x * b) (by simp [loopTwoCycleRelationSet])
  have hab : q (a * b) = 0 := hmkZero _ <|
    relationGenerator_mem x a b (a * b) (by simp [loopTwoCycleRelationSet])
  have hxba : q (x * (b * a)) = 0 := hmkZero _ <|
    jacobsonCube_le_relationIdeal x a b <| by
      simpa only [mul_assoc] using triple_mem_jacobsonCube hxJ hbJ haJ
  have haba : q (a * (b * a)) = 0 := hmkZero _ <|
    jacobsonCube_le_relationIdeal x a b <| by
      simpa only [mul_assoc] using triple_mem_jacobsonCube haJ hbJ haJ
  have hbba : q (b * (b * a)) = 0 := hmkZero _ <|
    jacobsonCube_le_relationIdeal x a b <| by
      simpa only [mul_assoc] using triple_mem_jacobsonCube hbJ hbJ haJ
  have hbax : q ((b * a) * x) = 0 := hmkZero _ <|
    jacobsonCube_le_relationIdeal x a b (triple_mem_jacobsonCube hbJ haJ hxJ)
  have hbaa : q ((b * a) * a) = 0 := hmkZero _ <|
    jacobsonCube_le_relationIdeal x a b (triple_mem_jacobsonCube hbJ haJ haJ)
  have hbab : q ((b * a) * b) = 0 := hmkZero _ <|
    jacobsonCube_le_relationIdeal x a b (triple_mem_jacobsonCube hbJ haJ hbJ)
  have hbaba : q ((b * a) * (b * a)) = 0 := by
    apply hmkZero
    apply jacobsonCube_le_relationIdeal x a b
    have h4 : (b * a) * (b * a) ∈ (Ring.jacobson B) ^ 4 := by
      rw [show (4 : ℕ) = 2 + 2 by omega, Ideal.IsTwoSided.pow_add]
      apply Ideal.mul_mem_mul
      · rw [show (2 : ℕ) = 1 + 1 by omega, Ideal.IsTwoSided.pow_add,
          Submodule.pow_one]
        exact Ideal.mul_mem_mul hbJ haJ
      · rw [show (2 : ℕ) = 1 + 1 by omega, Ideal.IsTwoSided.pow_add,
          Submodule.pow_one]
        exact Ideal.mul_mem_mul hbJ haJ
    exact Ideal.pow_le_pow_right (by omega : 3 ≤ 4) h4
  dsimp only
  intro i j
  cases i <;> cases j <;>
    simp only [SixCoordinateBasisQuotientData.basisProduct,
      SixBasisIndex.productIndex, sixPeirceElements]
  all_goals change q (_ * _) = _
  · exact congrArg q he₀e₀
  · rw [he₀e₁, map_zero]
  · exact congrArg q hxleft
  · rw [he₀a, map_zero]
  · exact congrArg q hbleft
  · exact congrArg q he₀ba
  · rw [he₁e₀, map_zero]
  · exact congrArg q he₁e₁
  · rw [he₁x, map_zero]
  · exact congrArg q haleft
  · rw [he₁b, map_zero]
  · rw [he₁ba, map_zero]
  · exact congrArg q hxright
  · rw [hxe₁, map_zero]
  · exact hxx
  · rw [hxa, map_zero]
  · exact hxb
  · exact hxba
  · exact congrArg q haright
  · rw [hae₁, map_zero]
  · exact hax
  · rw [haa, map_zero]
  · exact hab
  · exact haba
  · rw [hbe₀, map_zero]
  · exact congrArg q hbright
  · rw [hbx, map_zero]
  · rfl
  · rw [hbb, map_zero]
  · exact hbba
  · exact congrArg q hbae₀
  · rw [hbae₁, map_zero]
  · exact hbax
  · exact hbaa
  · exact hbab
  · exact hbaba

/-- Cotangent spanning, survival of `b*a`, and the Peirce support identities
construct the complete six-coordinate quotient package. -/
noncomputable def sixCoordinateBasisQuotientData_of_cotangentSpanned
    [FiniteDimensional K B]
    {x a b : B}
    (hxJ : x ∈ Ring.jacobson B)
    (haJ : a ∈ Ring.jacobson B)
    (hbJ : b ∈ Ring.jacobson B)
    (hxleft : D.liftedCoordinate 0 * x = x)
    (hxright : x * D.liftedCoordinate 0 = x)
    (haleft : D.liftedCoordinate 1 * a = a)
    (haright : a * D.liftedCoordinate 0 = a)
    (hbleft : D.liftedCoordinate 0 * b = b)
    (hbright : b * D.liftedCoordinate 1 = b)
    (hx2 : x ∉ (Ring.jacobson B) ^ 2)
    (ha2 : a ∉ (Ring.jacobson B) ^ 2)
    (hb2 : b ∉ (Ring.jacobson B) ^ 2)
    (hcyclic : OpConjecture.Tsukamoto.cyclicRightIdealFG (b * a) ≅
      OpConjecture.Tsukamoto.cyclicRightIdealFG x)
    (hspan : JacobsonCotangentSpannedBy (K := K) x a b) :
    SixCoordinateBasisQuotientData K B
      (B ⧸ relationIdeal x a b) := by
  let H := relationIdeal x a b
  let q : B →+* B ⧸ H := Ideal.Quotient.mk H
  let v : SixBasisIndex → B ⧸ H := fun i ↦
    Ideal.Quotient.mk H (D.sixPeirceElements x a b i)
  have hIndependent : LinearIndependent K v := by
    exact D.six_relationQuotientClasses_linearIndependent_of_cotangentSpanned
      hxJ haJ hbJ hxleft hxright haleft haright hbleft hbright
        hx2 ha2 hb2 hcyclic hspan
  have hSpans : ⊤ ≤ Submodule.span K (Set.range v) := by
    exact D.six_relationQuotientClasses_span_of_cotangentSpanned
      hxJ haJ hbJ hxleft hxright haleft haright hbleft hbright hspan
  have hOne : 1 = v .e₁ + v .e₂ := by
    change Ideal.Quotient.mk H 1 =
      Ideal.Quotient.mk H (D.liftedCoordinate 0) +
        Ideal.Quotient.mk H (D.liftedCoordinate 1)
    rw [← map_add]
    congr 1
    simpa [Fin.sum_univ_two] using D.liftedCoordinate_complete.complete.symm
  have hMul : ∀ i j,
      v i * v j = SixCoordinateBasisQuotientData.basisProduct v i j := by
    exact D.six_relationQuotientClasses_mul hxJ haJ hbJ
      hxleft hxright haleft haright hbleft hbright
  exact SixCoordinateBasisQuotientData.ofLinearIndependentSpanningRelations
    q Ideal.Quotient.mk_surjective v hIndependent hSpans hOne hMul

/-- The numerical cotangent bound used in the manuscript automatically
constructs the complete six-coordinate quotient package. -/
noncomputable def sixCoordinateBasisQuotientData_of_finrank_le_three
    [FiniteDimensional K B]
    {x a b : B}
    (hxJ : x ∈ Ring.jacobson B)
    (haJ : a ∈ Ring.jacobson B)
    (hbJ : b ∈ Ring.jacobson B)
    (hxleft : D.liftedCoordinate 0 * x = x)
    (hxright : x * D.liftedCoordinate 0 = x)
    (haleft : D.liftedCoordinate 1 * a = a)
    (haright : a * D.liftedCoordinate 0 = a)
    (hbleft : D.liftedCoordinate 0 * b = b)
    (hbright : b * D.liftedCoordinate 1 = b)
    (hx2 : x ∉ (Ring.jacobson B) ^ 2)
    (ha2 : a ∉ (Ring.jacobson B) ^ 2)
    (hb2 : b ∉ (Ring.jacobson B) ^ 2)
    (hcyclic : OpConjecture.Tsukamoto.cyclicRightIdealFG (b * a) ≅
      OpConjecture.Tsukamoto.cyclicRightIdealFG x)
    (hdim : CotangentDimensionAtMostThree (K := K) (B := B)) :
    SixCoordinateBasisQuotientData K B
      (B ⧸ relationIdeal x a b) :=
  D.sixCoordinateBasisQuotientData_of_cotangentSpanned
    hxJ haJ hbJ hxleft hxright haleft haright hbleft hbright
      hx2 ha2 hb2 hcyclic
      (D.jacobsonCotangentSpannedBy_of_finrank_le_three
        hxJ haJ hbJ hxleft hxright haleft haright hbleft hbright
          hx2 ha2 hb2 hdim)

/-- Paper-facing exclusion of the loop-plus-two-cycle branch.  The
six-dimensional relation quotient carries an infinite family of pairwise
nonisomorphic indecomposables, contradicting any finite complete right-module
skeleton of the source algebra. -/
theorem false_of_loopTwoCycle_of_finrank_le_three
    [FiniteDimensional K B] [Infinite K]
    {x a b : B}
    (hxJ : x ∈ Ring.jacobson B)
    (haJ : a ∈ Ring.jacobson B)
    (hbJ : b ∈ Ring.jacobson B)
    (hxleft : D.liftedCoordinate 0 * x = x)
    (hxright : x * D.liftedCoordinate 0 = x)
    (haleft : D.liftedCoordinate 1 * a = a)
    (haright : a * D.liftedCoordinate 0 = a)
    (hbleft : D.liftedCoordinate 0 * b = b)
    (hbright : b * D.liftedCoordinate 1 = b)
    (hx2 : x ∉ (Ring.jacobson B) ^ 2)
    (ha2 : a ∉ (Ring.jacobson B) ^ 2)
    (hb2 : b ∉ (Ring.jacobson B) ^ 2)
    (hcyclic : OpConjecture.Tsukamoto.cyclicRightIdealFG (b * a) ≅
      OpConjecture.Tsukamoto.cyclicRightIdealFG x)
    (hdim : CotangentDimensionAtMostThree (K := K) (B := B)) :
    letI : IsNoetherianRing Bᵐᵒᵖ := IsNoetherianRing.of_finite K Bᵐᵒᵖ
    ∀ {iota : Type v} [Finite iota],
      OpConjecture.IndecomposableSkeleton.{u, v, u} Bᵐᵒᵖ iota → False := by
  letI : IsNoetherianRing Bᵐᵒᵖ := IsNoetherianRing.of_finite K Bᵐᵒᵖ
  intro iota _ sigma
  exact
    (D.sixCoordinateBasisQuotientData_of_finrank_le_three
      hxJ haJ hbJ hxleft hxright haleft haright hbleft hbright
        hx2 ha2 hb2 hcyclic hdim).false_of_right_finite_skeleton sigma

end OpConjecture.QuotientSurvival.TwoCoordinateData
