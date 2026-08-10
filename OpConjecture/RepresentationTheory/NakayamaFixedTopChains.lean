import OpConjecture.RepresentationTheory.NakayamaProjectiveQuotients
import OpConjecture.RepresentationTheory.NakayamaChainClosureAdapter

/-!
# Fixed-top chains for a uniserial indecomposable skeleton

A finite-length uniserial projective has a uniserial quotient of every
positive length up to its composition length.  For a finite complete
uniserial indecomposable skeleton, these quotients give the exact fixed-top
chain parametrization used by the Nakayama theorem.
-/

noncomputable section

open Set CategoryTheory

namespace OpConjecture.NakayamaFixedTopChains

universe u v

variable {R : Type u} [Ring R]

/-- A finite-length uniserial module has a quotient of every positive length
up to its own composition length. -/
theorem exists_quotient_of_length
    {M : Type u} [AddCommGroup M] [Module R M]
    [Module.Finite R M]
    (hfinite : IsFiniteLength R M)
    (hM : IsUniserialModule R M)
    {n : ℕ} (hn : 0 < n)
    (hnle : (n : ℕ∞) ≤ Module.length R M) :
    ∃ N : Submodule R M,
      Module.length R (M ⧸ N) = n ∧
        IsUniserialModule R (M ⧸ N) := by
  obtain ⟨s, hsbot, hstop⟩ :=
    isFiniteLength_iff_exists_compositionSeries.mp hfinite
  have hslen : (s.length : ℕ∞) = Module.length R M :=
    Module.length_compositionSeries s hsbot hstop
  have hnle' : n ≤ s.length := by
    rw [← hslen] at hnle
    exact_mod_cast hnle
  let t : LTSeries (Submodule R M) :=
    s.map ⟨id, fun h ↦ h.1⟩
  let i : Fin (t.length + 1) :=
    ⟨t.length - n, by
      dsimp [t]
      omega⟩
  let N : Submodule R M := t i
  have htmax : (t.length : ℕ∞) = Order.coheight t.head := by
    change (s.length : ℕ∞) = Order.coheight (id s.head)
    rw [id_eq, hsbot, ← Module.length_eq_coheight, hslen]
  have hNcoheight : Order.coheight N = n := by
    change Order.coheight (t i) = n
    rw [Order.coheight_eq_index_of_length_eq_head_coheight htmax]
    norm_cast
    simp only [i, Fin.val_rev]
    simp only [t, RelSeries.map_length]
    omega
  refine ⟨N, ?_, hM.quotient N⟩
  rw [Module.length_quotient, hNcoheight]

open OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank

variable [IsNoetherianRing R]
  {ι : Type v}
  (σ : IndecomposableSkeleton.{u, v, u} R ι)

/-- Capacity of the fixed-top chain indexed by a chosen simple: the
composition length of its chosen indecomposable projective cover. -/
def fixedTopCapacity (j : σ.SimpleIndex) : ℕ :=
  σ.compositionLength (projectiveLabelOfSimple σ j)

/-- The selected simple-top label of the chosen projective cover is the
simple which indexed that cover. -/
theorem uniserialTopIndex_projectiveLabelOfSimple
    (hNakayama : ∀ i : ι, IsUniserialModule R (σ.obj i))
    (j : σ.SimpleIndex) :
    OpConjecture.NakayamaProjectiveQuotients.uniserialTopIndex σ
        (projectiveLabelOfSimple σ j)
        (hNakayama (projectiveLabelOfSimple σ j)) = j := by
  let p : ProjectiveIndex σ :=
    (projectiveIndexEquivSimpleIndex σ).symm j
  have hpTop : projectiveTopIndex σ p = j :=
    (projectiveIndexEquivSimpleIndex σ).apply_symm_apply j
  apply Subtype.ext
  apply σ.eq_of_iso
  let eSelected :=
    OpConjecture.NakayamaProjectiveQuotients.uniserialTopIso σ
      (projectiveLabelOfSimple σ j)
      (hNakayama (projectiveLabelOfSimple σ j))
  let eProjective :
      FGModuleCat.of R
          (σ.moduleTop (projectiveLabelOfSimple σ j)) ≅
        σ.obj j.1 :=
    (projectiveTopIso σ p) ≪≫
      eqToIso
        (congrArg (fun s : σ.SimpleIndex ↦ σ.obj s.1) hpTop)
  exact ⟨eSelected.symm ≪≫ eProjective⟩

/-- Every positive coordinate in a fixed-top projective chain is realized by
an indecomposable quotient with exactly that top and composition length. -/
theorem exists_fixedTop_quotient_label
    (hNakayama : ∀ i : ι, IsUniserialModule R (σ.obj i))
    (j : σ.SimpleIndex) {n : ℕ}
    (hn : 0 < n) (hnle : n ≤ fixedTopCapacity σ j) :
    ∃ k : ι,
      (∃ f :
          σ.obj (projectiveLabelOfSimple σ j) ⟶ σ.obj k,
        Epi f) ∧
      OpConjecture.NakayamaProjectiveQuotients.uniserialTopIndex σ k
          (hNakayama k) = j ∧
      σ.compositionLength k = n := by
  let p : ι := projectiveLabelOfSimple σ j
  have hnle' : (n : ℕ∞) ≤ Module.length R (σ.obj p) := by
    rw [← σ.coe_compositionLength p]
    exact_mod_cast hnle
  obtain ⟨N, hNlength, hNuniserial⟩ :=
    exists_quotient_of_length
      (σ.finiteLength p) (hNakayama p) hn hnle'
  let Q : FGModuleCat.{u} R :=
    FGModuleCat.of R ((σ.obj p) ⧸ N)
  have hQpos : (0 : ℕ∞) < Module.length R Q := by
    change (0 : ℕ∞) < Module.length R ((σ.obj p) ⧸ N)
    rw [hNlength]
    exact_mod_cast hn
  letI : Nontrivial Q := Module.length_pos_iff.mp hQpos
  have hQindec : OpConjecture.Foundation.IsIndecomposableModule R Q :=
    hNuniserial.isIndecomposableModule
  obtain ⟨k, ⟨e⟩⟩ := σ.complete Q hQindec
  let q : σ.obj p ⟶ Q := FGModuleCat.ofHom N.mkQ
  haveI : Epi q :=
    (IndecomposableSkeleton.fg_epi_iff_surjective q).mpr
      N.mkQ_surjective
  let f : σ.obj p ⟶ σ.obj k := q ≫ e.hom
  haveI : Epi f := by
    dsimp [f]
    infer_instance
  have htop :
      OpConjecture.NakayamaProjectiveQuotients.uniserialTopIndex σ k
          (hNakayama k) = j := by
    rw [← uniserialTopIndex_projectiveLabelOfSimple σ hNakayama j]
    exact
      (OpConjecture.NakayamaProjectiveQuotients.uniserialTopIndex_eq_of_epi
        σ p k (hNakayama p) (hNakayama k) f).symm
  have hlength : σ.compositionLength k = n := by
    rw [← ENat.coe_inj, σ.coe_compositionLength]
    calc
      Module.length R (σ.obj k) = Module.length R Q :=
        (FGModuleCat.isoToLinearEquiv e).length_eq.symm
      _ = Module.length R ((σ.obj p) ⧸ N) := rfl
      _ = n := hNlength
  exact ⟨k, ⟨f, inferInstance⟩, htop, hlength⟩

/-- A chosen skeleton label at each fixed-top chain coordinate. -/
def fixedTopLabel
    (hNakayama : ∀ i : ι, IsUniserialModule R (σ.obj i))
    (p : OpConjecture.NakayamaCombinatorics.ChainPoint
      (fixedTopCapacity σ)) : ι :=
  Classical.choose
    (exists_fixedTop_quotient_label σ hNakayama p.1
      (n := (p.2 : ℕ) + 1) (by omega) (by
        exact Nat.succ_le_iff.mpr p.2.isLt))

theorem fixedTopLabel_epi
    (hNakayama : ∀ i : ι, IsUniserialModule R (σ.obj i))
    (p : OpConjecture.NakayamaCombinatorics.ChainPoint
      (fixedTopCapacity σ)) :
    ∃ f : σ.obj (projectiveLabelOfSimple σ p.1) ⟶
        σ.obj (fixedTopLabel σ hNakayama p),
      Epi f :=
  (Classical.choose_spec
    (exists_fixedTop_quotient_label σ hNakayama p.1
      (n := (p.2 : ℕ) + 1) (by omega) (by
        exact Nat.succ_le_iff.mpr p.2.isLt))).1

theorem fixedTopLabel_topIndex
    (hNakayama : ∀ i : ι, IsUniserialModule R (σ.obj i))
    (p : OpConjecture.NakayamaCombinatorics.ChainPoint
      (fixedTopCapacity σ)) :
    OpConjecture.NakayamaProjectiveQuotients.uniserialTopIndex σ
        (fixedTopLabel σ hNakayama p)
        (hNakayama (fixedTopLabel σ hNakayama p)) = p.1 :=
  (Classical.choose_spec
    (exists_fixedTop_quotient_label σ hNakayama p.1
      (n := (p.2 : ℕ) + 1) (by omega) (by
        exact Nat.succ_le_iff.mpr p.2.isLt))).2.1

theorem fixedTopLabel_compositionLength
    (hNakayama : ∀ i : ι, IsUniserialModule R (σ.obj i))
    (p : OpConjecture.NakayamaCombinatorics.ChainPoint
      (fixedTopCapacity σ)) :
    σ.compositionLength (fixedTopLabel σ hNakayama p) =
      (p.2 : ℕ) + 1 :=
  (Classical.choose_spec
    (exists_fixedTop_quotient_label σ hNakayama p.1
      (n := (p.2 : ℕ) + 1) (by omega) (by
        exact Nat.succ_le_iff.mpr p.2.isLt))).2.2

theorem fixedTopLabel_injective
    (hNakayama : ∀ i : ι, IsUniserialModule R (σ.obj i)) :
    Function.Injective (fixedTopLabel σ hNakayama) := by
  rintro ⟨j, a⟩ ⟨k, b⟩ hab
  have hjk : j = k := by
    have ha := fixedTopLabel_topIndex σ hNakayama ⟨j, a⟩
    have hb := fixedTopLabel_topIndex σ hNakayama ⟨k, b⟩
    rw [hab] at ha
    exact ha.symm.trans hb
  subst k
  congr 1
  apply Fin.ext
  have ha := fixedTopLabel_compositionLength σ hNakayama ⟨j, a⟩
  have hb := fixedTopLabel_compositionLength σ hNakayama ⟨j, b⟩
  have hlen : (a : ℕ) + 1 = (b : ℕ) + 1 := by
    calc
      (a : ℕ) + 1 =
          σ.compositionLength (fixedTopLabel σ hNakayama ⟨j, a⟩) :=
        ha.symm
      _ = σ.compositionLength (fixedTopLabel σ hNakayama ⟨j, b⟩) :=
        congrArg σ.compositionLength hab
      _ = (b : ℕ) + 1 := hb
  omega

theorem fixedTopLabel_surjective
    (hNakayama : ∀ i : ι, IsUniserialModule R (σ.obj i)) :
    Function.Surjective (fixedTopLabel σ hNakayama) := by
  intro i
  let j :=
    OpConjecture.NakayamaProjectiveQuotients.uniserialTopIndex σ i
      (hNakayama i)
  obtain ⟨f, hf⟩ :=
    OpConjecture.NakayamaProjectiveQuotients.exists_epi_projectiveLabelOfSimple_of_top_iso
      σ i (hNakayama i) j
      (OpConjecture.NakayamaProjectiveQuotients.uniserialTopIso σ i
        (hNakayama i))
  letI : Epi f := hf
  have hle : σ.compositionLength i ≤ fixedTopCapacity σ j := by
    exact σ.compositionLength_le_of_epi f
  let p : OpConjecture.NakayamaCombinatorics.ChainPoint
      (fixedTopCapacity σ) :=
    ⟨j, ⟨σ.compositionLength i - 1, by
      have hpos := σ.compositionLength_pos i
      dsimp [fixedTopCapacity] at hle ⊢
      omega⟩⟩
  refine ⟨p, ?_⟩
  let eTopLabel :
      FGModuleCat.of R
          (σ.moduleTop (fixedTopLabel σ hNakayama p)) ≅
        σ.obj j.1 :=
    OpConjecture.NakayamaProjectiveQuotients.uniserialTopIso σ
        (fixedTopLabel σ hNakayama p)
        (hNakayama (fixedTopLabel σ hNakayama p)) ≪≫
      eqToIso
        (congrArg (fun s : σ.SimpleIndex ↦ σ.obj s.1)
          (fixedTopLabel_topIndex σ hNakayama p))
  have hlength :
      σ.compositionLength (fixedTopLabel σ hNakayama p) =
        σ.compositionLength i := by
    rw [fixedTopLabel_compositionLength]
    dsimp [p]
    have hpos := σ.compositionLength_pos i
    omega
  exact
    OpConjecture.NakayamaProjectiveQuotients.eq_of_top_iso_of_compositionLength_eq_of_projective_uniserial
      σ j (hNakayama (projectiveLabelOfSimple σ j))
      (fixedTopLabel σ hNakayama p) i
      (hNakayama (fixedTopLabel σ hNakayama p)) (hNakayama i)
      eTopLabel
      (OpConjecture.NakayamaProjectiveQuotients.uniserialTopIso σ i
        (hNakayama i))
      hlength

/-- The chosen fixed-top labels are a complete duplicate-free enumeration of
the indecomposable skeleton. -/
def fixedTopLabelEquiv
    (hNakayama : ∀ i : ι, IsUniserialModule R (σ.obj i)) :
    OpConjecture.NakayamaCombinatorics.ChainPoint
        (fixedTopCapacity σ) ≃ ι :=
  Equiv.ofBijective (fixedTopLabel σ hNakayama)
    ⟨fixedTopLabel_injective σ hNakayama,
      fixedTopLabel_surjective σ hNakayama⟩

open OpConjecture.NakayamaCombinatorics

/-- Singleton downward closure in a chain says precisely: same chain index
and weakly smaller numeric coordinate. -/
theorem mem_chainClosure_singleton_iff
    {κ : Type*} {c : κ → ℕ} (p q : ChainPoint c) :
    q ∈ chainClosure c ({p} : Set (ChainPoint c)) ↔
      q.1 = p.1 ∧ (q.2 : ℕ) ≤ (p.2 : ℕ) := by
  rcases p with ⟨ip, jp⟩
  rcases q with ⟨iq, jq⟩
  constructor
  · rintro ⟨k, hk, hjk⟩
    have hi : iq = ip := congrArg Sigma.fst hk
    subst ip
    have hk' : k = jp := by
      exact Fin.ext (congrArg (fun z : ChainPoint c ↦ (z.2 : ℕ)) hk)
    subst k
    exact ⟨rfl, by exact_mod_cast hjk⟩
  · rintro ⟨hi, hj⟩
    change iq = ip at hi
    subst ip
    exact ⟨jp, by simp, by exact_mod_cast hj⟩

theorem fixedTopLabelEquiv_symm_first
    (hNakayama : ∀ i : ι, IsUniserialModule R (σ.obj i))
    (i : ι) :
    ((fixedTopLabelEquiv σ hNakayama).symm i).1 =
      OpConjecture.NakayamaProjectiveQuotients.uniserialTopIndex σ i
        (hNakayama i) := by
  let p := (fixedTopLabelEquiv σ hNakayama).symm i
  have hp := fixedTopLabel_topIndex σ hNakayama p
  have he : fixedTopLabel σ hNakayama p = i :=
    (fixedTopLabelEquiv σ hNakayama).apply_symm_apply i
  rw [he] at hp
  exact hp.symm

theorem fixedTopLabelEquiv_symm_compositionLength
    (hNakayama : ∀ i : ι, IsUniserialModule R (σ.obj i))
    (i : ι) :
    σ.compositionLength i =
      (((fixedTopLabelEquiv σ hNakayama).symm i).2 : ℕ) + 1 := by
  let p := (fixedTopLabelEquiv σ hNakayama).symm i
  have hp := fixedTopLabel_compositionLength σ hNakayama p
  have he : fixedTopLabel σ hNakayama p = i :=
    (fixedTopLabelEquiv σ hNakayama).apply_symm_apply i
  rwa [he] at hp

/-- The quotient relation transported through the fixed-top labeling is
exactly singleton downward closure. -/
theorem exists_epi_iff_fixedTop_chainClosure
    (hNakayama : ∀ i : ι, IsUniserialModule R (σ.obj i))
    (i k : ι) :
    (∃ f : σ.obj i ⟶ σ.obj k, Epi f) ↔
      (fixedTopLabelEquiv σ hNakayama).symm k ∈
        chainClosure (fixedTopCapacity σ)
          ({(fixedTopLabelEquiv σ hNakayama).symm i} :
            Set (ChainPoint (fixedTopCapacity σ))) := by
  rw [OpConjecture.NakayamaProjectiveQuotients.exists_epi_iff_topIndex_eq_and_compositionLength_le]
  rw [mem_chainClosure_singleton_iff]
  have hiTop := fixedTopLabelEquiv_symm_first σ hNakayama i
  have hkTop := fixedTopLabelEquiv_symm_first σ hNakayama k
  have hiLength :=
    fixedTopLabelEquiv_symm_compositionLength σ hNakayama i
  have hkLength :=
    fixedTopLabelEquiv_symm_compositionLength σ hNakayama k
  constructor
  · rintro ⟨htop, hlength⟩
    constructor
    · rw [hiTop, hkTop]
      exact htop.symm
    · omega
  · rintro ⟨htop, hlength⟩
    constructor
    · rw [← hiTop, ← hkTop]
      exact htop.symm
    · omega

/-- Complete fixed-top chain data for any uniserial indecomposable
skeleton. -/
def fixedTopChainData
    [Fintype σ.SimpleIndex]
    (hNakayama : ∀ i : ι, IsUniserialModule R (σ.obj i)) :
    OpConjecture.NakayamaModuleChains.FixedTopChainData σ
      (fixedTopCapacity σ) where
  labelEquiv := fixedTopLabelEquiv σ hNakayama
  uniserial := hNakayama
  epi_iff := exists_epi_iff_fixedTop_chainClosure σ hNakayama


end OpConjecture.NakayamaFixedTopChains
