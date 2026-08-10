import QuotientSubmoduleEquidistribution.RepresentationTheory.LollipopB1Modules
import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# A seven-block normal form for the live-path lollipop

For a finite representation `(L,T)` with `L^2=0`, put `N=ker T`,
`Z=ker L`, and `E=range L`.  The two subspaces

* `M=L(N) <= E`, and
* `K=E \cap N <= E`

split the Jordan blocks into the four regions `X,U,W,P`.  Complements in
`N \cap Z`, `Z`, and the target supply the `S1`, `A`, and `S2` regions.
This file makes that simultaneous splitting explicit over an arbitrary
field.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

namespace QuotientSubmoduleEquidistribution.LollipopConcrete.B1.ModuleLayer.ExhaustivenessReduction

universe u

variable (K : Type u) [Field K]

abbrev loopMap (D : FiniteB1Rep K) : D.V₁ →ₗ[K] D.V₁ :=
  D.loop.hom.hom

abbrev stemMap (D : FiniteB1Rep K) : D.V₁ →ₗ[K] D.V₂ :=
  D.stem.hom.hom

def loopRange (D : FiniteB1Rep K) : Submodule K D.V₁ :=
  LinearMap.range (loopMap K D)

def loopKernel (D : FiniteB1Rep K) : Submodule K D.V₁ :=
  LinearMap.ker (loopMap K D)

def stemKernel (D : FiniteB1Rep K) : Submodule K D.V₁ :=
  LinearMap.ker (stemMap K D)

def deadKernel (D : FiniteB1Rep K) : Submodule K D.V₁ :=
  stemKernel K D ⊓ loopKernel K D

theorem loopRange_le_loopKernel (D : FiniteB1Rep K) :
    loopRange K D ≤ loopKernel K D := by
  rintro _ ⟨v, rfl⟩
  exact D.loop_sq v

/-- The loop image, restricted to vectors killed by the stem. -/
def killedBottom (D : FiniteB1Rep K) :
    Submodule K (loopRange K D) :=
  LinearMap.ker ((stemMap K D).comp (loopRange K D).subtype)

/-- The loop on the stem kernel, with codomain restricted to its range. -/
def loopOnStemKernel (D : FiniteB1Rep K) :
    stemKernel K D →ₗ[K] loopRange K D :=
  LinearMap.codRestrict (loopRange K D)
    ((loopMap K D).comp (stemKernel K D).subtype)
    (fun v ↦ ⟨v.1, rfl⟩)

/-- Bottom vectors admitting a loop-top preimage killed by the stem. -/
def mobileBottom (D : FiniteB1Rep K) :
    Submodule K (loopRange K D) :=
  LinearMap.range (loopOnStemKernel K D)

/-- Jordan blocks whose top and bottom are both killed by the stem. -/
def xBottom (D : FiniteB1Rep K) :
    Submodule K (loopRange K D) :=
  mobileBottom K D ⊓ killedBottom K D

/-- The literal ambient copy of `E \cap N`. -/
def deadBottomAmbient (D : FiniteB1Rep K) : Submodule K D.V₁ :=
  loopRange K D ⊓ stemKernel K D

theorem deadBottomAmbient_le_deadKernel (D : FiniteB1Rep K) :
    deadBottomAmbient K D ≤ deadKernel K D := by
  intro v hv
  exact ⟨hv.2, loopRange_le_loopKernel K D hv.1⟩

/-- A simultaneous choice of all seven multiplicity spaces. -/
structure SplittingFlag (D : FiniteB1Rep K) where
  /-- `X ⊕ U = L(ker T)`. -/
  uBottom : Submodule K (loopRange K D)
  x_u_disjoint : Disjoint (xBottom K D) uBottom
  x_sup_u : xBottom K D ⊔ uBottom = mobileBottom K D
  /-- `X ⊕ W = range L ∩ ker T`. -/
  wBottom : Submodule K (loopRange K D)
  x_w_disjoint : Disjoint (xBottom K D) wBottom
  x_sup_w : xBottom K D ⊔ wBottom = killedBottom K D
  /-- `(L(ker T) ⊕ W) ⊕ P = range L`. -/
  pBottom : Submodule K (loopRange K D)
  mobile_w_p_compl :
    IsCompl (mobileBottom K D ⊔ wBottom) pBottom
  /-- `(E ∩ N) ⊕ S1 = N ∩ Z`. -/
  s1Space : Submodule K D.V₁
  dead_s1_disjoint : Disjoint (deadBottomAmbient K D) s1Space
  dead_sup_s1 : deadBottomAmbient K D ⊔ s1Space = deadKernel K D
  /-- `(E ⊕ S1) ⊕ A = Z`. -/
  aSpace : Submodule K D.V₁
  es1_a_disjoint : Disjoint (loopRange K D ⊔ s1Space) aSpace
  es1_sup_a : (loopRange K D ⊔ s1Space) ⊔ aSpace = loopKernel K D
  /-- A complement to `N ∩ Z` inside `N`; the loop identifies it with
  `L(N)`. -/
  nTop : Submodule K D.V₁
  dead_nTop_disjoint : Disjoint (deadKernel K D) nTop
  dead_sup_nTop : deadKernel K D ⊔ nTop = stemKernel K D
  /-- A global loop-top complement extending `nTop`. -/
  loopTop : Submodule K D.V₁
  nTop_le_loopTop : nTop ≤ loopTop
  loopTop_compl : IsCompl loopTop (loopKernel K D)
  /-- The `S2` target complement. -/
  residualTail : Submodule K D.V₂
  stemRange_tail_compl :
    IsCompl (LinearMap.range (stemMap K D)) residualTail

/-- Every finite live-path representation has a seven-space splitting flag. -/
theorem exists_splittingFlag (D : FiniteB1Rep K) :
    Nonempty (SplittingFlag K D) := by
  have hxM : xBottom K D ≤ mobileBottom K D := inf_le_left
  obtain ⟨U, hxU, hXU⟩ :=
    IsModularLattice.exists_disjoint_and_sup_eq hxM
  have hxK : xBottom K D ≤ killedBottom K D := inf_le_right
  obtain ⟨W, hxW, hXW⟩ :=
    IsModularLattice.exists_disjoint_and_sup_eq hxK
  obtain ⟨P, hMWP⟩ :=
    (mobileBottom K D ⊔ W).exists_isCompl
  obtain ⟨S, hdeadS, hDS⟩ :=
    IsModularLattice.exists_disjoint_and_sup_eq
      (deadBottomAmbient_le_deadKernel K D)
  have hESZ : loopRange K D ⊔ S ≤ loopKernel K D := by
    rw [sup_le_iff]
    refine ⟨loopRange_le_loopKernel K D, ?_⟩
    intro s hs
    have hsDead : s ∈ deadKernel K D := by
      rw [← hDS]
      exact Submodule.mem_sup_right hs
    exact hsDead.2
  obtain ⟨A, hESA, hESAsup⟩ :=
    IsModularLattice.exists_disjoint_and_sup_eq hESZ
  have hDN : deadKernel K D ≤ stemKernel K D := inf_le_left
  obtain ⟨NT, hDNT, hDNTsup⟩ :=
    IsModularLattice.exists_disjoint_and_sup_eq hDN
  have hNTZ : Disjoint NT (loopKernel K D) := by
    rw [Submodule.disjoint_def]
    intro v hvNT hvZ
    have hvN : v ∈ stemKernel K D := by
      rw [← hDNTsup]
      exact Submodule.mem_sup_right hvNT
    have hvD : v ∈ deadKernel K D := ⟨hvN, hvZ⟩
    exact Submodule.disjoint_def.mp hDNT v hvD hvNT
  obtain ⟨LT, hNTLT, hLT⟩ := hNTZ.exists_isCompl
  obtain ⟨Q, hQ⟩ := (LinearMap.range (stemMap K D)).exists_isCompl
  exact ⟨{
    uBottom := U
    x_u_disjoint := hxU
    x_sup_u := hXU
    wBottom := W
    x_w_disjoint := hxW
    x_sup_w := hXW
    pBottom := P
    mobile_w_p_compl := hMWP
    s1Space := S
    dead_s1_disjoint := hdeadS
    dead_sup_s1 := hDS
    aSpace := A
    es1_a_disjoint := hESA
    es1_sup_a := hESAsup
    nTop := NT
    dead_nTop_disjoint := hDNT
    dead_sup_nTop := hDNTsup
    loopTop := LT
    nTop_le_loopTop := hNTLT
    loopTop_compl := hLT
    residualTail := Q
    stemRange_tail_compl := hQ }⟩

namespace SplittingFlag

variable {K}

theorem uBottom_le_mobile (D : FiniteB1Rep K)
    (F : SplittingFlag K D) : F.uBottom ≤ mobileBottom K D := by
  rw [← F.x_sup_u]
  exact le_sup_right

theorem wBottom_le_killed (D : FiniteB1Rep K)
    (F : SplittingFlag K D) : F.wBottom ≤ killedBottom K D := by
  rw [← F.x_sup_w]
  exact le_sup_right

theorem mobile_w_disjoint (D : FiniteB1Rep K)
    (F : SplittingFlag K D) :
    Disjoint (mobileBottom K D) F.wBottom := by
  rw [Submodule.disjoint_def]
  intro z hzM hzW
  have hzK : z ∈ killedBottom K D := wBottom_le_killed D F hzW
  have hzX : z ∈ xBottom K D := ⟨hzM, hzK⟩
  exact Submodule.disjoint_def.mp F.x_w_disjoint z hzX hzW

/-- `M` is complementary to `W ⊕ P` inside the loop range. -/
theorem mobile_rest_compl (D : FiniteB1Rep K)
    (F : SplittingFlag K D) :
    IsCompl (mobileBottom K D) (F.wBottom ⊔ F.pBottom) :=
  (mobile_w_disjoint D F).isCompl_sup_right_of_isCompl_sup_left
    F.mobile_w_p_compl

theorem s1Space_le_deadKernel (D : FiniteB1Rep K)
    (F : SplittingFlag K D) : F.s1Space ≤ deadKernel K D := by
  rw [← F.dead_sup_s1]
  exact le_sup_right

theorem s1Space_le_stemKernel (D : FiniteB1Rep K)
    (F : SplittingFlag K D) : F.s1Space ≤ stemKernel K D :=
  (s1Space_le_deadKernel D F).trans inf_le_left

theorem s1Space_le_loopKernel (D : FiniteB1Rep K)
    (F : SplittingFlag K D) : F.s1Space ≤ loopKernel K D :=
  (s1Space_le_deadKernel D F).trans inf_le_right

theorem aSpace_le_loopKernel (D : FiniteB1Rep K)
    (F : SplittingFlag K D) : F.aSpace ≤ loopKernel K D := by
  rw [← F.es1_sup_a]
  exact le_sup_right

theorem nTop_le_stemKernel (D : FiniteB1Rep K)
    (F : SplittingFlag K D) : F.nTop ≤ stemKernel K D := by
  rw [← F.dead_sup_nTop]
  exact le_sup_right

/-! ### Relative direct-sum coordinates -/

/-- Repack a subspace as its copy inside a larger subspace. -/
def equivComapOfLe {V : Type*} [AddCommGroup V] [Module K V]
    {P S : Submodule K V} (hPS : P ≤ S) :
    P ≃ₗ[K] P.comap S.subtype where
  toFun p := ⟨⟨p.1, hPS p.2⟩, p.2⟩
  invFun p := ⟨p.1.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem relative_isCompl {V : Type*} [AddCommGroup V] [Module K V]
    {P Q S : Submodule K V}
    (hPS : P ≤ S) (hQS : Q ≤ S)
    (hPQ : Disjoint P Q) (hsup : P ⊔ Q = S) :
    IsCompl (P.comap S.subtype) (Q.comap S.subtype) := by
  apply IsCompl.of_eq
  · have hd : Disjoint (P.comap S.subtype) (Q.comap S.subtype) := by
      rw [Submodule.disjoint_def]
      intro z hzP hzQ
      apply Subtype.ext
      exact Submodule.disjoint_def.mp hPQ z.1 hzP hzQ
    exact hd.eq_bot
  · apply top_unique
    intro z _
    have hz : (z.1 : V) ∈ P ⊔ Q := by
      rw [hsup]
      exact z.2
    rcases Submodule.mem_sup.mp hz with ⟨p, hp, q, hq, hpq⟩
    apply Submodule.mem_sup.mpr
    refine ⟨⟨p, hPS hp⟩, hp, ⟨q, hQS hq⟩, hq, ?_⟩
    apply Subtype.ext
    exact hpq

/-- If `P ⊕ Q = S` as ambient subspaces, addition gives `P × Q ≃ S`. -/
def relativeProdEquiv {V : Type*} [AddCommGroup V] [Module K V]
    {P Q S : Submodule K V}
    (hPS : P ≤ S) (hQS : Q ≤ S)
    (hPQ : Disjoint P Q) (hsup : P ⊔ Q = S) :
    (P × Q) ≃ₗ[K] S :=
  ((equivComapOfLe hPS).prodCongr (equivComapOfLe hQS)).trans
    ((P.comap S.subtype).prodEquivOfIsCompl
      (Q.comap S.subtype)
      (relative_isCompl hPS hQS hPQ hsup))

@[simp] theorem relativeProdEquiv_apply
    {V : Type*} [AddCommGroup V] [Module K V]
    {P Q S : Submodule K V}
    (hPS : P ≤ S) (hQS : Q ≤ S)
    (hPQ : Disjoint P Q) (hsup : P ⊔ Q = S)
    (z : P × Q) :
    relativeProdEquiv hPS hQS hPQ hsup z =
      ⟨z.1.1 + z.2.1, add_mem (hPS z.1.2) (hQS z.2.2)⟩ := rfl

abbrev xSpace (D : FiniteB1Rep K) := xBottom K D
abbrev uSpace (D : FiniteB1Rep K) (F : SplittingFlag K D) := F.uBottom
abbrev wSpace (D : FiniteB1Rep K) (F : SplittingFlag K D) := F.wBottom
abbrev pSpace (D : FiniteB1Rep K) (F : SplittingFlag K D) := F.pBottom

/-- One multiplicity coordinate for the top (or bottom) of every Jordan
block, ordered as `X,U,W,P`. -/
abbrev JordanCoords (D : FiniteB1Rep K) (F : SplittingFlag K D) :=
  ((xSpace D × uSpace D F) × wSpace D F) × pSpace D F

def xuEquivMobile (D : FiniteB1Rep K) (F : SplittingFlag K D) :
    (xSpace D × uSpace D F) ≃ₗ[K] mobileBottom K D :=
  relativeProdEquiv inf_le_left (uBottom_le_mobile D F)
    F.x_u_disjoint F.x_sup_u

def mobileWEquiv (D : FiniteB1Rep K) (F : SplittingFlag K D) :
    (mobileBottom K D × wSpace D F) ≃ₗ[K]
      (mobileBottom K D ⊔ F.wBottom :
        Submodule K (loopRange K D)) :=
  relativeProdEquiv le_sup_left le_sup_right
    (mobile_w_disjoint D F) rfl

/-- The four Jordan multiplicity spaces add up to the entire loop range. -/
def jordanEquivLoopRange (D : FiniteB1Rep K) (F : SplittingFlag K D) :
    JordanCoords D F ≃ₗ[K] loopRange K D :=
  (((xuEquivMobile D F).prodCongr (LinearEquiv.refl K (wSpace D F))).prodCongr
      (LinearEquiv.refl K (pSpace D F))).trans
    (((mobileWEquiv D F).prodCongr
      (LinearEquiv.refl K (pSpace D F))).trans
        ((mobileBottom K D ⊔ F.wBottom :
          Submodule K (loopRange K D)).prodEquivOfIsCompl
          F.pBottom F.mobile_w_p_compl))

@[simp] theorem jordanEquivLoopRange_apply_coe (D : FiniteB1Rep K)
    (F : SplittingFlag K D) (z : JordanCoords D F) :
    (jordanEquivLoopRange D F z : D.V₁) =
      z.1.1.1.1 + z.1.1.2.1 + z.1.2.1 + z.2.1 := rfl

/-! ### Vertex-one normal coordinates -/

/-- The chosen loop top is identified with the complete loop range. -/
def loopTopEquivRange (D : FiniteB1Rep K) (F : SplittingFlag K D) :
    F.loopTop ≃ₗ[K] loopRange K D :=
  LinearMap.kerComplementEquivRange (loopMap K D) F.loopTop_compl

@[simp] theorem loopTopEquivRange_apply_coe (D : FiniteB1Rep K)
    (F : SplittingFlag K D) (b : F.loopTop) :
    ((loopTopEquivRange D F b : loopRange K D) : D.V₁) =
      loopMap K D b.1 := rfl

/-- Since the global loop top extends the chosen complement inside `ker T`,
the inverse section over `L(ker T)` is itself killed by `T`. -/
theorem loopTopEquivRange_symm_mobile_mem_stemKernel
    (D : FiniteB1Rep K) (F : SplittingFlag K D)
    (m : mobileBottom K D) :
    ((loopTopEquivRange D F).symm (m.1 : loopRange K D) : D.V₁) ∈
      stemKernel K D := by
  rcases m.2 with ⟨n, hn⟩
  have hnN : (n.1 : D.V₁) ∈ stemKernel K D := n.2
  have hnSup : (n.1 : D.V₁) ∈ deadKernel K D ⊔ F.nTop := by
    rw [F.dead_sup_nTop]
    exact hnN
  rcases Submodule.mem_sup.mp hnSup with ⟨d, hd, t, ht, hdt⟩
  let tt : F.loopTop := ⟨t, F.nTop_le_loopTop ht⟩
  have hloopd : loopMap K D d = 0 := hd.2
  have hloopt : loopMap K D t = (m.1 : D.V₁) := by
    have hnval := congrArg Subtype.val hn
    change loopMap K D n.1 = (m.1 : D.V₁) at hnval
    rw [← hdt, map_add, hloopd, zero_add] at hnval
    exact hnval
  have htt : loopTopEquivRange D F tt = (m.1 : loopRange K D) := by
    apply Subtype.ext
    exact hloopt
  have heq : (loopTopEquivRange D F).symm (m.1 : loopRange K D) = tt := by
    rw [← htt, (loopTopEquivRange D F).symm_apply_apply]
  rw [heq]
  have htN : t ∈ stemKernel K D := by
    rw [← F.dead_sup_nTop]
    exact Submodule.mem_sup_right ht
  exact htN

theorem loopRange_s1_disjoint (D : FiniteB1Rep K)
    (F : SplittingFlag K D) :
    Disjoint (loopRange K D) F.s1Space := by
  rw [Submodule.disjoint_def]
  intro z hzE hzS
  have hzN : z ∈ stemKernel K D := s1Space_le_stemKernel D F hzS
  have hzDead : z ∈ deadBottomAmbient K D := ⟨hzE, hzN⟩
  exact Submodule.disjoint_def.mp F.dead_s1_disjoint z hzDead hzS

def loopRangeS1Equiv (D : FiniteB1Rep K) (F : SplittingFlag K D) :
    (loopRange K D × F.s1Space) ≃ₗ[K]
      (loopRange K D ⊔ F.s1Space : Submodule K D.V₁) :=
  relativeProdEquiv le_sup_left le_sup_right
    (loopRange_s1_disjoint D F) rfl

/-- Kernel coordinates, ordered as one lower coordinate for every Jordan
block, followed by `S1` and `A`. -/
abbrev KernelCoords (D : FiniteB1Rep K) (F : SplittingFlag K D) :=
  (JordanCoords D F × F.s1Space) × F.aSpace

def kernelEquivLoopKernel (D : FiniteB1Rep K)
    (F : SplittingFlag K D) :
    KernelCoords D F ≃ₗ[K] loopKernel K D :=
  (((jordanEquivLoopRange D F).prodCongr
      (LinearEquiv.refl K F.s1Space)).prodCongr
        (LinearEquiv.refl K F.aSpace)).trans
    (((loopRangeS1Equiv D F).prodCongr
      (LinearEquiv.refl K F.aSpace)).trans
        (relativeProdEquiv
          (by
            rw [sup_le_iff]
            exact ⟨loopRange_le_loopKernel K D,
              s1Space_le_loopKernel D F⟩)
          (aSpace_le_loopKernel D F)
          F.es1_a_disjoint F.es1_sup_a))

@[simp] theorem kernelEquivLoopKernel_apply_coe (D : FiniteB1Rep K)
    (F : SplittingFlag K D) (z : KernelCoords D F) :
    (kernelEquivLoopKernel D F z : D.V₁) =
      z.1.1.1.1.1 + z.1.1.1.1.2.1 + z.1.1.1.2.1 +
        z.1.1.2.1 + z.1.2.1 + z.2.1 := by
  simp only [kernelEquivLoopKernel, LinearEquiv.trans_apply,
    LinearEquiv.prodCongr_apply, loopRangeS1Equiv,
    relativeProdEquiv_apply, LinearEquiv.refl_apply]
  rw [jordanEquivLoopRange_apply_coe]

/-- Complete vertex-one normal coordinates. -/
abbrev NormalV₁ (D : FiniteB1Rep K) (F : SplittingFlag K D) :=
  JordanCoords D F × KernelCoords D F

/-- The complete vertex-one coordinate change. -/
def normalV₁Equiv (D : FiniteB1Rep K) (F : SplittingFlag K D) :
    NormalV₁ D F ≃ₗ[K] D.V₁ :=
  (((jordanEquivLoopRange D F).trans
      (loopTopEquivRange D F).symm).prodCongr
    (kernelEquivLoopKernel D F)).trans
      (F.loopTop.prodEquivOfIsCompl (loopKernel K D) F.loopTop_compl)

@[simp] theorem normalV₁Equiv_apply (D : FiniteB1Rep K)
    (F : SplittingFlag K D) (z : NormalV₁ D F) :
    normalV₁Equiv D F z =
      ((loopTopEquivRange D F).symm
          (jordanEquivLoopRange D F z.1) : D.V₁) +
        (kernelEquivLoopKernel D F z.2 : D.V₁) := rfl

/-- Square-zero loop in the normal coordinates: every top coordinate is
sent to the corresponding lower coordinate. -/
def normalLoop (D : FiniteB1Rep K) (F : SplittingFlag K D) :
    NormalV₁ D F →ₗ[K] NormalV₁ D F where
  toFun z := (0, ((z.1, 0), 0))
  map_add' z w := by
    ext <;> simp
  map_smul' c z := by
    ext <;> simp

@[simp] theorem normalLoop_apply (D : FiniteB1Rep K)
    (F : SplittingFlag K D) (z : NormalV₁ D F) :
    normalLoop D F z = (0, ((z.1, 0), 0)) := by
  rfl

theorem normalLoop_sq (D : FiniteB1Rep K) (F : SplittingFlag K D)
    (z : NormalV₁ D F) :
    normalLoop D F (normalLoop D F z) = 0 := by
  ext <;> rfl

/-- The vertex-one coordinate change intertwines the normal and original
loop maps. -/
theorem normalV₁Equiv_loop (D : FiniteB1Rep K)
    (F : SplittingFlag K D) (z : NormalV₁ D F) :
    normalV₁Equiv D F (normalLoop D F z) =
      loopMap K D (normalV₁Equiv D F z) := by
  rw [normalV₁Equiv_apply, normalV₁Equiv_apply]
  simp only [normalLoop_apply, map_add, map_zero]
  rw [kernelEquivLoopKernel_apply_coe]
  have htop := (loopTopEquivRange D F).apply_symm_apply
    (jordanEquivLoopRange D F z.1)
  have htop' := congrArg (fun q : loopRange K D ↦ (q : D.V₁)) htop
  change loopMap K D
      (((loopTopEquivRange D F).symm
        (jordanEquivLoopRange D F z.1) : F.loopTop) : D.V₁) =
    (jordanEquivLoopRange D F z.1 : D.V₁) at htop'
  rw [htop']
  have hker : loopMap K D (kernelEquivLoopKernel D F z.2 : D.V₁) = 0 :=
    (kernelEquivLoopKernel D F z.2).2
  rw [hker, add_zero]
  rw [jordanEquivLoopRange_apply_coe]
  simp

/-! ### Stem-active coordinates -/

/-- The target coordinate associated to each non-kernel source direction:
`U` lower, `W` top, the two `P` directions, and `A`. -/
abbrev StemCoords (D : FiniteB1Rep K) (F : SplittingFlag K D) :=
  ((uSpace D F × wSpace D F) × (pSpace D F × pSpace D F)) ×
    F.aSpace

def activeTopCoords (D : FiniteB1Rep K) (F : SplittingFlag K D)
    (c : StemCoords D F) : JordanCoords D F :=
  (((0, 0), c.1.1.2), c.1.2.2)

def activeBottomCoords (D : FiniteB1Rep K) (F : SplittingFlag K D)
    (c : StemCoords D F) : JordanCoords D F :=
  (((0, c.1.1.1), 0), c.1.2.1)

/-- Embed the stem-active directions into the complete normal vertex-one
coordinates. -/
def activeEmbed (D : FiniteB1Rep K) (F : SplittingFlag K D) :
    StemCoords D F →ₗ[K] NormalV₁ D F where
  toFun c :=
    (activeTopCoords D F c,
      ((activeBottomCoords D F c, 0), c.2))
  map_add' c d := by
    ext <;> simp [activeTopCoords, activeBottomCoords]
  map_smul' c z := by
    ext <;> simp [activeTopCoords, activeBottomCoords]

@[simp] theorem activeEmbed_apply (D : FiniteB1Rep K)
    (F : SplittingFlag K D) (c : StemCoords D F) :
    activeEmbed D F c =
      (activeTopCoords D F c, ((activeBottomCoords D F c, 0), c.2)) := rfl

/-- Projection onto the stem-active normal coordinates. -/
def activeProjection (D : FiniteB1Rep K) (F : SplittingFlag K D) :
    NormalV₁ D F →ₗ[K] StemCoords D F where
  toFun z :=
    (((z.2.1.1.1.1.2, z.1.1.2), (z.2.1.1.2, z.1.2)), z.2.2)
  map_add' z w := by
    ext <;> simp
  map_smul' c z := by
    ext <;> simp

@[simp] theorem activeProjection_activeEmbed (D : FiniteB1Rep K)
    (F : SplittingFlag K D) (c : StemCoords D F) :
    activeProjection D F (activeEmbed D F c) = c := by
  rfl

/-- The actual source vector represented by the active coordinates. -/
def activeSource (D : FiniteB1Rep K) (F : SplittingFlag K D) :
    StemCoords D F →ₗ[K] D.V₁ :=
  (normalV₁Equiv D F).toLinearMap.comp (activeEmbed D F)

@[simp] theorem activeSource_apply (D : FiniteB1Rep K)
    (F : SplittingFlag K D) (c : StemCoords D F) :
    activeSource D F c = normalV₁Equiv D F (activeEmbed D F c) := rfl

theorem activeSource_injective (D : FiniteB1Rep K)
    (F : SplittingFlag K D) : Function.Injective (activeSource D F) := by
  intro c d hcd
  have hembed : activeEmbed D F c = activeEmbed D F d :=
    (normalV₁Equiv D F).injective hcd
  simpa only [activeProjection_activeEmbed] using
    congrArg (activeProjection D F) hembed

/-- Applying the loop to an active source keeps precisely its `W`-top and
`P`-top lower coordinates. -/
theorem loop_activeSource (D : FiniteB1Rep K)
    (F : SplittingFlag K D) (c : StemCoords D F) :
    loopMap K D (activeSource D F c) =
      (jordanEquivLoopRange D F (activeTopCoords D F c) : D.V₁) := by
  rw [activeSource_apply, ← normalV₁Equiv_loop]
  rw [normalV₁Equiv_apply]
  simp only [normalLoop_apply, activeEmbed, map_zero]
  rw [kernelEquivLoopKernel_apply_coe]
  simp [activeTopCoords]

/-- The lower `U/P` directions are disjoint from the stem-dead lower
directions `X/W`. -/
theorem killedBottom_disjoint_activeBottom (D : FiniteB1Rep K)
    (F : SplittingFlag K D) :
    Disjoint (killedBottom K D) (F.uBottom ⊔ F.pBottom) := by
  rw [Submodule.disjoint_def]
  intro z hzKilled hzActive
  have hzXW : z ∈ xBottom K D ⊔ F.wBottom := by
    rw [F.x_sup_w]
    exact hzKilled
  rcases Submodule.mem_sup.mp hzXW with ⟨x, hx, w, hw, hxw⟩
  rcases Submodule.mem_sup.mp hzActive with ⟨u, hu, p, hp, hup⟩
  let jk : JordanCoords D F :=
    (((⟨x, hx⟩, 0), ⟨w, hw⟩), 0)
  let ja : JordanCoords D F :=
    (((0, ⟨u, hu⟩), 0), ⟨p, hp⟩)
  have himages : jordanEquivLoopRange D F jk =
      jordanEquivLoopRange D F ja := by
    apply Subtype.ext
    rw [jordanEquivLoopRange_apply_coe,
      jordanEquivLoopRange_apply_coe]
    simpa [jk, ja] using congrArg Subtype.val (hxw.trans hup.symm)
  have hcoords : jk = ja := (jordanEquivLoopRange D F).injective himages
  have huZero : (⟨u, hu⟩ : F.uBottom) = 0 := by
    have h := congrArg (fun q : JordanCoords D F ↦ q.1.1.2) hcoords
    exact h.symm
  have hpZero : (⟨p, hp⟩ : F.pBottom) = 0 := by
    have h := congrArg (fun q : JordanCoords D F ↦ q.2) hcoords
    exact h.symm
  have huVal : u = 0 := congrArg Subtype.val huZero
  have hpVal : p = 0 := congrArg Subtype.val hpZero
  rw [← hup, huVal, hpVal, zero_add]

theorem activeTop_mem_rest (D : FiniteB1Rep K)
    (F : SplittingFlag K D) (c : StemCoords D F) :
    jordanEquivLoopRange D F (activeTopCoords D F c) ∈
      F.wBottom ⊔ F.pBottom := by
  apply Submodule.mem_sup.mpr
  refine ⟨c.1.1.2.1, c.1.1.2.2, c.1.2.2.1, c.1.2.2.2, ?_⟩
  apply Subtype.ext
  rw [jordanEquivLoopRange_apply_coe]
  simp [activeTopCoords]

theorem activeBottom_mem_active (D : FiniteB1Rep K)
    (F : SplittingFlag K D) (c : StemCoords D F) :
    jordanEquivLoopRange D F (activeBottomCoords D F c) ∈
      F.uBottom ⊔ F.pBottom := by
  apply Submodule.mem_sup.mpr
  refine ⟨c.1.1.1.1, c.1.1.1.2, c.1.2.1.1, c.1.2.1.2, ?_⟩
  apply Subtype.ext
  rw [jordanEquivLoopRange_apply_coe]
  simp [activeBottomCoords]

theorem deadKernel_le_range_s1 (D : FiniteB1Rep K)
    (F : SplittingFlag K D) :
    deadKernel K D ≤ loopRange K D ⊔ F.s1Space := by
  rw [← F.dead_sup_s1]
  apply sup_le
  · exact inf_le_left.trans le_sup_left
  · exact le_sup_right

/-- The stem is injective on the selected `U,W,P,P,A` source coordinates. -/
theorem activeStem_injective (D : FiniteB1Rep K)
    (F : SplittingFlag K D) :
    Function.Injective ((stemMap K D).comp (activeSource D F)) := by
  refine (injective_iff_map_eq_zero _).mpr ?_
  intro c hcStem
  have hsourceN : activeSource D F c ∈ stemKernel K D := hcStem
  let eTop : loopRange K D :=
    jordanEquivLoopRange D F (activeTopCoords D F c)
  have heTopMobile : eTop ∈ mobileBottom K D := by
    refine ⟨⟨activeSource D F c, hsourceN⟩, ?_⟩
    apply Subtype.ext
    exact loop_activeSource D F c
  have heTopRest : eTop ∈ F.wBottom ⊔ F.pBottom :=
    activeTop_mem_rest D F c
  have heTopZero : eTop = 0 :=
    Submodule.disjoint_def.mp (mobile_rest_compl D F).disjoint
      eTop heTopMobile heTopRest
  have hTopZero : activeTopCoords D F c = 0 := by
    apply (jordanEquivLoopRange D F).injective
    simpa [eTop] using heTopZero
  have hloopZero : loopMap K D (activeSource D F c) = 0 := by
    rw [loop_activeSource, hTopZero, map_zero]
    rfl
  have hsourceDead : activeSource D F c ∈ deadKernel K D :=
    ⟨hsourceN, hloopZero⟩
  let eBottom : loopRange K D :=
    jordanEquivLoopRange D F (activeBottomCoords D F c)
  have hsourceForm : activeSource D F c =
      (eBottom : D.V₁) + c.2.1 := by
    rw [activeSource_apply, normalV₁Equiv_apply]
    rw [activeEmbed_apply, hTopZero, map_zero]
    rw [kernelEquivLoopKernel_apply_coe]
    simp [eBottom, activeBottomCoords]
  have hsourceES : activeSource D F c ∈
      loopRange K D ⊔ F.s1Space :=
    deadKernel_le_range_s1 D F hsourceDead
  have heBottomES : (eBottom : D.V₁) ∈
      loopRange K D ⊔ F.s1Space :=
    (show loopRange K D ≤ loopRange K D ⊔ F.s1Space from
      le_sup_left) eBottom.2
  have haES : (c.2.1 : D.V₁) ∈
      loopRange K D ⊔ F.s1Space := by
    have hsub := Submodule.sub_mem
      (loopRange K D ⊔ F.s1Space) hsourceES heBottomES
    have heq : activeSource D F c - (eBottom : D.V₁) =
        (c.2.1 : D.V₁) := by
      rw [hsourceForm]
      abel
    rwa [heq] at hsub
  have haValZero : (c.2.1 : D.V₁) = 0 :=
    Submodule.disjoint_def.mp F.es1_a_disjoint
      (c.2.1 : D.V₁) haES c.2.2
  have haZero : c.2 = 0 := by
    apply Subtype.ext
    exact haValZero
  have hsourceEqBottom : activeSource D F c = (eBottom : D.V₁) := by
    rw [hsourceForm, haValZero, add_zero]
  have heBottomKilled : eBottom ∈ killedBottom K D := by
    change stemMap K D (eBottom : D.V₁) = 0
    rw [← hsourceEqBottom]
    exact hsourceN
  have heBottomActive : eBottom ∈ F.uBottom ⊔ F.pBottom :=
    activeBottom_mem_active D F c
  have heBottomZero : eBottom = 0 :=
    Submodule.disjoint_def.mp (killedBottom_disjoint_activeBottom D F)
      eBottom heBottomKilled heBottomActive
  have hBottomZero : activeBottomCoords D F c = 0 := by
    apply (jordanEquivLoopRange D F).injective
    simpa [eBottom] using heBottomZero
  have hEmbedZero : activeEmbed D F c = 0 := by
    simp [activeEmbed, hTopZero, hBottomZero, haZero]
  have hcZero := congrArg (activeProjection D F) hEmbedZero
  simpa only [activeProjection_activeEmbed, map_zero] using hcZero

end SplittingFlag

end QuotientSubmoduleEquidistribution.LollipopConcrete.B1.ModuleLayer.ExhaustivenessReduction
