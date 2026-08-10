import QuotientSubmoduleEquidistribution.RepresentationTheory.MoritaBasicizationInterface
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.Data.Matrix.PEquiv

/-!
# Ring-theoretic Morita basicization

This file proves the existence of a full idempotent with basic corner for every
finite-dimensional algebra over an algebraically closed field.  The explicit
categorical equivalence for such an idempotent is supplied separately in
`FullIdempotentMorita`.
-/

noncomputable section

open scoped BigOperators

namespace QuotientSubmoduleEquidistribution.MoritaBasicizationInterface

universe u v

theorem nilIdeal_le_jacobson {R : Type u} [Ring R]
    (I : Ideal R) [I.IsTwoSided]
    (hI : ∀ x ∈ I, IsNilpotent x) :
    I ≤ Ring.jacobson R := by
  intro x hx
  rw [← Ideal.jacobson_bot, Ideal.mem_jacobson_iff]
  intro y
  have hyx : IsNilpotent (y * x) := hI _ (I.mul_mem_left y hx)
  have hu : IsUnit (1 + y * x) := by
    simpa only [sub_neg_eq_add] using hyx.neg.isUnit_one_sub
  obtain ⟨z, hz⟩ := hu.exists_left_inv
  refine ⟨z, ?_⟩
  rw [Submodule.mem_bot]
  calc
    z * y * x + z - 1 = z * (1 + y * x) - 1 := by noncomm_ring
    _ = 0 := by rw [hz, sub_self]

theorem full_lift_of_surjective
    {R : Type u} {S : Type v} [Ring R] [Ring S]
    (f : R →+* S) (hf : Function.Surjective f)
    (hnil : ∀ x ∈ RingHom.ker f, IsNilpotent x)
    {e : R} {p : S} (hep : f e = p)
    (hp : IsFullElem p) :
    IsFullElem e := by
  obtain ⟨n, a, b, hab⟩ := hp
  choose a' ha' using fun i ↦ hf (a i)
  choose b' hb' using fun i ↦ hf (b i)
  let w : R := ∑ i, a' i * e * b' i
  have hfw : f w = 1 := by
    simp only [w, map_sum, map_mul, ha', hb', hep, hab]
  have hker : 1 - w ∈ RingHom.ker f := by
    rw [RingHom.mem_ker, map_sub, map_one, hfw, sub_self]
  have hw : IsUnit w := by
    simpa only [sub_sub_cancel] using (hnil _ hker).isUnit_one_sub
  obtain ⟨c, hc⟩ := hw.exists_left_inv
  refine ⟨n, fun i ↦ c * a' i, b', ?_⟩
  calc
    ∑ i, (c * a' i) * e * b' i = c * w := by
      simp only [w, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [mul_assoc]
    _ = 1 := hc

theorem isFullElem_map_ringEquiv
    {R : Type u} {S : Type v} [Ring R] [Ring S]
    (E : R ≃+* S) {e : R} (he : IsFullElem e) :
    IsFullElem (E e) := by
  obtain ⟨n, a, b, hab⟩ := he
  refine ⟨n, fun i ↦ E (a i), fun i ↦ E (b i), ?_⟩
  calc
    ∑ i, E (a i) * E e * E (b i) = ∑ i, E (a i * e * b i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [map_mul, map_mul]
    _ = E (∑ i, a i * e * b i) := by rw [map_sum]
    _ = 1 := by rw [hab, map_one]

def cornerMap
    {R : Type u} {S : Type v} [Ring R] [Ring S]
    (f : R →+* S) {e : R} {p : S}
    (he : IsIdempotentElem e) (hp : IsIdempotentElem p)
    (hep : f e = p) :
    he.Corner →+* hp.Corner where
  toFun x := ⟨f x.1, by
    rcases x.2 with ⟨r, hr⟩
    refine ⟨f r, ?_⟩
    change p * f r * p = f x.1
    rw [← hr]
    simp only [map_mul, hep]⟩
  map_one' := by
    apply Subtype.ext
    exact hep
  map_mul' _ _ := by
    apply Subtype.ext
    exact map_mul f _ _
  map_zero' := by
    apply Subtype.ext
    exact map_zero f
  map_add' _ _ := by
    apply Subtype.ext
    exact map_add f _ _

theorem cornerMap_surjective
    {R : Type u} {S : Type v} [Ring R] [Ring S]
    (f : R →+* S) (hf : Function.Surjective f)
    {e : R} {p : S}
    (he : IsIdempotentElem e) (hp : IsIdempotentElem p)
    (hep : f e = p) :
    Function.Surjective (cornerMap f he hp hep) := by
  rintro ⟨y, hy⟩
  rcases hy with ⟨s, rfl⟩
  obtain ⟨r, rfl⟩ := hf s
  refine ⟨⟨e * r * e, r, rfl⟩, ?_⟩
  apply Subtype.ext
  change f (e * r * e) = p * f r * p
  simp only [map_mul, hep]

theorem cornerMap_kernel_nilpotent
    {R : Type u} {S : Type v} [Ring R] [Ring S]
    (f : R →+* S)
    (hnil : ∀ x ∈ RingHom.ker f, IsNilpotent x)
    {e : R} {p : S}
    (he : IsIdempotentElem e) (hp : IsIdempotentElem p)
    (hep : f e = p) :
    ∀ x ∈ RingHom.ker (cornerMap f he hp hep), IsNilpotent x := by
  intro x hx
  have hxval : x.1 ∈ RingHom.ker f := by
    rw [RingHom.mem_ker] at hx ⊢
    exact congrArg Subtype.val hx
  obtain ⟨n, hn⟩ := hnil x.1 hxval
  refine ⟨n, ?_⟩
  rcases n with _ | n
  · apply Subtype.ext
    change e = 0
    have hR : (1 : R) = 0 := by simpa using hn
    calc
      e = e * 1 := by rw [mul_one]
      _ = e * 0 := by rw [hR]
      _ = 0 := by rw [mul_zero]
  · apply Subtype.ext
    have hpow : (x ^ (n + 1) : he.Corner).1 = x.1 ^ (n + 1) := by
      clear hn
      induction n with
      | zero =>
          change (x ^ 1 : he.Corner).1 = x.1 ^ 1
          rw [pow_one, pow_one]
      | succ n ih =>
          calc
            (x ^ (Nat.succ n + 1) : he.Corner).1 =
                ((x ^ (n + 1)) * x : he.Corner).1 := by
                  rw [show Nat.succ n + 1 = (n + 1) + 1 by omega,
                    pow_succ]
            _ = (x ^ (n + 1) : he.Corner).1 * x.1 := rfl
            _ = x.1 ^ (n + 1) * x.1 := by rw [ih]
            _ = x.1 ^ ((n + 1) + 1) := (pow_succ x.1 (n + 1)).symm
            _ = x.1 ^ (Nat.succ n + 1) := by rfl
    exact hpow.trans hn

theorem corner_quotient_mul_comm_of_map
    {R : Type u} {S : Type v} [Ring R] [Ring S]
    (f : R →+* S) (hf : Function.Surjective f)
    (hnil : ∀ x ∈ RingHom.ker f, IsNilpotent x)
    {e : R} {p : S}
    (he : IsIdempotentElem e) (hp : IsIdempotentElem p)
    (hep : f e = p)
    (hcomm : ∀ x y : hp.Corner, x * y = y * x) :
    ∀ x y : he.Corner ⧸ Ring.jacobson he.Corner, x * y = y * x := by
  let g := cornerMap f he hp hep
  have hg : Function.Surjective g := cornerMap_surjective f hf he hp hep
  have hgNil : ∀ x ∈ RingHom.ker g, IsNilpotent x :=
    cornerMap_kernel_nilpotent f hnil he hp hep
  have hker : RingHom.ker g ≤ Ring.jacobson he.Corner :=
    nilIdeal_le_jacobson (RingHom.ker g) hgNil
  intro x y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_mul, ← map_mul, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  apply hker
  rw [RingHom.mem_ker, map_sub, map_mul, map_mul, hcomm, sub_self]

theorem corner_mul_comm_of_ringEquiv
    {R : Type u} {S : Type v} [Ring R] [Ring S]
    (E : R ≃+* S) {e : R} (he : IsIdempotentElem e)
    (hcomm : ∀ x y : (he.map E).Corner, x * y = y * x) :
    ∀ x y : he.Corner, x * y = y * x := by
  intro x y
  let x' : (he.map E).Corner :=
    cornerMap E.toRingHom he (he.map E) rfl x
  let y' : (he.map E).Corner :=
    cornerMap E.toRingHom he (he.map E) rfl y
  have hxy : E x.1 * E y.1 = E y.1 * E x.1 := by
    have h := congrArg Subtype.val (hcomm x' y')
    change E x.1 * E y.1 = E y.1 * E x.1 at h
    exact h
  apply Subtype.ext
  change x.1 * y.1 = y.1 * x.1
  apply E.injective
  simpa only [map_mul] using hxy

theorem corner_mul_comm_of_ringEquiv_eq
    {R : Type u} {S : Type v} [Ring R] [Ring S]
    (E : R ≃+* S) {e : R} {p : S}
    (he : IsIdempotentElem e) (hp : IsIdempotentElem p)
    (hep : E e = p)
    (hcomm : ∀ x y : hp.Corner, x * y = y * x) :
    ∀ x y : he.Corner, x * y = y * x := by
  intro x y
  let x' : hp.Corner := cornerMap E.toRingHom he hp hep x
  let y' : hp.Corner := cornerMap E.toRingHom he hp hep y
  have hxy : E x.1 * E y.1 = E y.1 * E x.1 := by
    have h := congrArg Subtype.val (hcomm x' y')
    change E x.1 * E y.1 = E y.1 * E x.1 at h
    exact h
  apply Subtype.ext
  change x.1 * y.1 = y.1 * x.1
  apply E.injective
  simpa only [map_mul] using hxy

structure QuotientBasicizingIdempotentData
    (K A : Type u) [Field K] [Ring A] [Algebra K A]
    [FiniteDimensional K A] where
  p : A ⧸ Ring.jacobson A
  idem : IsIdempotentElem p
  full : IsFullElem p
  corner_mul_comm : ∀ x y : idem.Corner, x * y = y * x

theorem element_nilpotent_of_mem_nilpotent_ideal
    {R : Type u} [Ring R] {I : Ideal R}
    (hI : IsNilpotent I) {x : R} (hx : x ∈ I) :
    IsNilpotent x := by
  obtain ⟨n, hn⟩ := hI
  refine ⟨n, ?_⟩
  have hxpow : x ^ n ∈ I ^ n := Ideal.pow_mem_pow hx n
  rw [hn] at hxpow
  exact hxpow

theorem exists_basicizingFullIdempotent_of_quotientData
    {K A : Type u} [Field K] [IsAlgClosed K]
    [Ring A] [Algebra K A] [FiniteDimensional K A]
    (P : QuotientBasicizingIdempotentData K A) :
    Nonempty (BasicizingFullIdempotent (K := K) (A := A)) := by
  letI : IsArtinianRing A := IsArtinianRing.of_finite K A
  let q : A →+* A ⧸ Ring.jacobson A :=
    Ideal.Quotient.mk (Ring.jacobson A)
  have hJ : IsNilpotent (Ring.jacobson A) := by
    rw [← Ideal.jacobson_bot]
    exact IsArtinianRing.isNilpotent_jacobson_bot
  have hqNil : ∀ x ∈ RingHom.ker q, IsNilpotent x := by
    intro x hx
    apply element_nilpotent_of_mem_nilpotent_ideal hJ
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← RingHom.mem_ker]
    exact hx
  obtain ⟨e, he, hep⟩ :=
    exists_isIdempotentElem_eq_of_ker_isNilpotent
      q hqNil P.p (Set.mem_range.mpr (Ideal.Quotient.mk_surjective P.p)) P.idem
  refine ⟨{
    e := e
    idem := he
    full := full_lift_of_surjective q Ideal.Quotient.mk_surjective hqNil hep P.full
    basic := ?_ }⟩
  letI : Algebra K he.Corner := cornerAlgebra (K := K) he
  letI : FiniteDimensional K he.Corner := cornerFiniteDimensional (K := K) he
  apply QuotientSubmoduleEquidistribution.BasicnessWrapper.isBasicAlgebra_of_quotient_mul_comm
    K he.Corner
  exact corner_quotient_mul_comm_of_map
    q Ideal.Quotient.mk_surjective hqNil he P.idem hep P.corner_mul_comm

section MatrixBasicization

variable (K : Type u) [Field K]
  {n : ℕ} (d : Fin n → ℕ) [∀ i, NeZero (d i)]

def basicMatrixIdempotent :
    ∀ i, Matrix (Fin (d i)) (Fin (d i)) K :=
  fun _ ↦ Matrix.single 0 0 1

def basicMatrixLeft (z : Σ i, Fin (d i)) :
    ∀ i, Matrix (Fin (d i)) (Fin (d i)) K :=
  Pi.single z.1 (Matrix.single z.2 0 1)

def basicMatrixRight (z : Σ i, Fin (d i)) :
    ∀ i, Matrix (Fin (d i)) (Fin (d i)) K :=
  Pi.single z.1 (Matrix.single 0 z.2 1)

theorem basicMatrixIdempotent_idem :
    IsIdempotentElem (basicMatrixIdempotent K d) := by
  rw [IsIdempotentElem]
  ext i a b
  by_cases ha : a = 0
  · subst a
    by_cases hb : b = 0
    · subst b
      simp [basicMatrixIdempotent, Matrix.mul_apply, Matrix.single]
    · simp [basicMatrixIdempotent, Matrix.mul_apply, Matrix.single, Ne.symm hb]
  · simp [basicMatrixIdempotent, Matrix.mul_apply, Matrix.single, Ne.symm ha]

theorem basicMatrixIdempotent_full :
    IsFullElem (basicMatrixIdempotent K d) := by
  let ι := Σ i, Fin (d i)
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι,
    fun k ↦ basicMatrixLeft K d (e k),
    fun k ↦ basicMatrixRight K d (e k), ?_⟩
  change (∑ k,
    basicMatrixLeft K d (e k) * basicMatrixIdempotent K d *
      basicMatrixRight K d (e k)) = 1
  rw [Equiv.sum_comp e (fun z ↦
    basicMatrixLeft K d z * basicMatrixIdempotent K d *
      basicMatrixRight K d z)]
  ext i a b
  rw [Fintype.sum_sigma]
  simp only [Finset.sum_apply, Matrix.sum_apply]
  rw [Finset.sum_eq_single i]
  · simp only [Pi.mul_apply, basicMatrixLeft, basicMatrixRight,
      basicMatrixIdempotent, Pi.single_eq_same, Pi.one_apply]
    by_cases hab : a = b
    · subst b
      simp only [Matrix.one_apply, if_pos]
      change (∑ x,
        ((((Matrix.single x 0 1 : Matrix (Fin (d i)) (Fin (d i)) K) *
            Matrix.single 0 0 1) * Matrix.single 0 x 1 :
              Matrix (Fin (d i)) (Fin (d i)) K) a a)) = 1
      simp_rw [Matrix.single_mul_single_same]
      simp [Matrix.single]
    · simp only [Matrix.one_apply, if_neg hab]
      change (∑ x,
        ((((Matrix.single x 0 1 : Matrix (Fin (d i)) (Fin (d i)) K) *
            Matrix.single 0 0 1) * Matrix.single 0 x 1 :
              Matrix (Fin (d i)) (Fin (d i)) K) a b)) = 0
      simp_rw [Matrix.single_mul_single_same]
      simp_all [Matrix.single]
      have hfin : ({x : Fin (d i) | x = a ∧ x = b} : Finset (Fin (d i))) = ∅ := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.notMem_empty, iff_false]
        rintro ⟨rfl, rfl⟩
        exact hab rfl
      rw [hfin]
      simp
  · intro j _ hji
    simp [basicMatrixLeft, basicMatrixRight, Ne.symm hji]
  · simp

theorem basicMatrixCorner_component_eq_single
    (x : (basicMatrixIdempotent_idem K d).Corner) (i : Fin n) :
    x.1 i = Matrix.single 0 0 (x.1 i 0 0) := by
  have hx := (Subsemigroup.mem_corner_iff
    (basicMatrixIdempotent_idem K d)).mp x.2
  ext a b
  by_cases ha : a = 0
  · subst a
    by_cases hb : b = 0
    · subst b
      simp [Matrix.single]
    · have hright := congrArg
        (fun z : ∀ i, Matrix (Fin (d i)) (Fin (d i)) K ↦ z i 0 b)
        hx.2
      have hzero : x.1 i 0 b = 0 := by
        symm
        simpa [basicMatrixIdempotent, Matrix.mul_apply, Matrix.single,
          Ne.symm hb] using hright
      simp [Matrix.single, Ne.symm hb, hzero]
  · have hleft := congrArg
      (fun z : ∀ i, Matrix (Fin (d i)) (Fin (d i)) K ↦ z i a b)
      hx.1
    have hzero : x.1 i a b = 0 := by
      symm
      simpa [basicMatrixIdempotent, Matrix.mul_apply, Matrix.single,
        Ne.symm ha] using hleft
    simp [Matrix.single, Ne.symm ha, hzero]

theorem basicMatrixCorner_mul_comm
    (x y : (basicMatrixIdempotent_idem K d).Corner) :
    x * y = y * x := by
  apply Subtype.ext
  ext i a b
  change (x.1 i * y.1 i) a b = (y.1 i * x.1 i) a b
  rw [basicMatrixCorner_component_eq_single K d x i,
    basicMatrixCorner_component_eq_single K d y i]
  rw [Matrix.single_mul_single_same, Matrix.single_mul_single_same]
  rw [mul_comm]

end MatrixBasicization

theorem exists_quotientBasicizingIdempotentData
    (K A : Type u) [Field K] [IsAlgClosed K]
    [Ring A] [Algebra K A] [FiniteDimensional K A] :
    Nonempty (QuotientBasicizingIdempotentData K A) := by
  let Q := A ⧸ Ring.jacobson A
  letI : IsArtinianRing A := IsArtinianRing.of_finite K A
  letI : FiniteDimensional K Q := inferInstance
  letI : IsSemisimpleRing Q := inferInstance
  obtain ⟨n, d, hd, ⟨E⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed K Q
  letI : ∀ i, NeZero (d i) := hd
  let p := basicMatrixIdempotent K d
  let hp : IsIdempotentElem p := basicMatrixIdempotent_idem K d
  let pQ : Q := E.symm p
  let hpQ : IsIdempotentElem pQ := hp.map E.symm
  refine ⟨{
    p := pQ
    idem := hpQ
    full := ?_
    corner_mul_comm := ?_ }⟩
  · exact isFullElem_map_ringEquiv E.symm.toRingEquiv
      (basicMatrixIdempotent_full K d)
  · exact corner_mul_comm_of_ringEquiv_eq E.toRingEquiv hpQ hp
      (E.apply_symm_apply p) (basicMatrixCorner_mul_comm K d)

theorem exists_basicizingFullIdempotent
    (K A : Type u) [Field K] [IsAlgClosed K]
    [Ring A] [Algebra K A] [FiniteDimensional K A] :
    Nonempty (BasicizingFullIdempotent (K := K) (A := A)) := by
  obtain ⟨P⟩ := exists_quotientBasicizingIdempotentData K A
  exact exists_basicizingFullIdempotent_of_quotientData P

theorem finiteDimensionalMoritaBasicization_of_fullIdempotentMoritaBridge
    (K : Type u) [Field K] [IsAlgClosed K]
    (hbridge : ∀ (A : Type u) [Ring A] [Algebra K A]
      [FiniteDimensional K A], FullIdempotentMoritaBridge (K := K) (A := A)) :
    FiniteDimensionalMoritaBasicization K := by
  intro A _ _ _
  exact (exists_basicizingFullIdempotent K A).map
    (MoritaBasicModel.ofBasicizingFullIdempotent (hbridge A))

end QuotientSubmoduleEquidistribution.MoritaBasicizationInterface
