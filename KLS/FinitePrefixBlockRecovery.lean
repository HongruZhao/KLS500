import KLS.BlockSymmetryInequality
import KLS.WeightedIterationTaylorPartialBound

/-! Literal initial and complementary coordinate block subgroups. The BKL
block inequality is transferred to averages over Fin-indexed prefixes. -/

open scoped BigOperators
noncomputable section
namespace KLS

def finPrefixSet (m p : ℕ) : Finset (Fin p) := Finset.univ.filter (fun i => i.val < m)

@[simp] theorem mem_finPrefixSet {m p : ℕ} (i : Fin p) :
    i ∈ finPrefixSet m p ↔ i.val < m := by simp [finPrefixSet]

def finPrefixSetEquiv {m p : ℕ} (h : m ≤ p) : Fin m ≃ finPrefixSet m p where
  toFun i := ⟨Fin.castLE h i, by simp [i.isLt]⟩
  invFun i := ⟨i.val.val, (mem_finPrefixSet i.val).mp i.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem finPrefixSet_card {m p : ℕ} (h : m ≤ p) : (finPrefixSet m p).card = m := by
  have hc := Fintype.card_congr (finPrefixSetEquiv h)
  simpa only [Fintype.card_fin, Fintype.card_coe] using hc.symm

theorem finPrefixSet_mono {d m p : ℕ} (h : d ≤ m) : finPrefixSet d p ⊆ finPrefixSet m p := by
  intro i hi
  exact (mem_finPrefixSet i).mpr (((mem_finPrefixSet i).mp hi).trans_le h)

theorem ofSubtype_finPrefixSetEquiv {m p : ℕ} (h : m ≤ p) (σ : Equiv.Perm (Fin m)) :
    Equiv.Perm.ofSubtype ((finPrefixSetEquiv h).permCongrHom σ) = prefixFinPermHom h σ := by
  apply Equiv.ext
  intro i
  by_cases hi : i.val < m
  · let j : Fin m := ⟨i.val, hi⟩
    have he : i = Fin.castLE h j := by apply Fin.ext; rfl
    rw [he, prefixFinPermHom_apply_castLE]
    exact Equiv.Perm.ofSubtype_apply_coe _ (finPrefixSetEquiv h j)
  · rw [Equiv.Perm.ofSubtype_apply_of_not_mem _ (by simpa using hi),
      prefixFinPermHom_apply_of_le h σ i (Nat.le_of_not_gt hi)]

def finPrefixComplementEquiv (d q : ℕ) :
    Fin q ≃ {i : Fin (d + q) // i ∉ finPrefixSet d (d + q)} where
  toFun j := ⟨Fin.natAdd d j, by simp⟩
  invFun i := ⟨i.val.val - d, by have hi := i.val.isLt; have hj := i.prop; simp only [mem_finPrefixSet] at hj; omega⟩
  left_inv j := by apply Fin.ext; simp
  right_inv i := by apply Subtype.ext; apply Fin.ext; have hj := i.prop; simp only [mem_finPrefixSet] at hj; simp; omega

def suffixFinPermHom (d q : ℕ) : Equiv.Perm (Fin q) →* Equiv.Perm (Fin (d + q)) :=
  (Equiv.Perm.ofSubtype : Equiv.Perm {i : Fin (d + q) // i ∉ finPrefixSet d (d + q)} →*
    Equiv.Perm (Fin (d + q))).comp (finPrefixComplementEquiv d q).permCongrHom.toMonoidHom

@[simp] theorem suffixFinPermHom_apply_natAdd (d q : ℕ) (σ : Equiv.Perm (Fin q)) (j : Fin q) :
    suffixFinPermHom d q σ (Fin.natAdd d j) = Fin.natAdd d (σ j) := by
  calc
    _ = (((finPrefixComplementEquiv d q).permCongrHom σ)
        (finPrefixComplementEquiv d q j)).val :=
      Equiv.Perm.ofSubtype_apply_coe _ (finPrefixComplementEquiv d q j)
    _ = (finPrefixComplementEquiv d q (σ j)).val := by
      congr 1
      change (finPrefixComplementEquiv d q) (σ ((finPrefixComplementEquiv d q).symm
        (finPrefixComplementEquiv d q j))) = _
      rw [Equiv.symm_apply_apply]
    _ = _ := rfl

@[simp] theorem suffixFinPermHom_apply_castAdd (d q : ℕ) (σ : Equiv.Perm (Fin q)) (j : Fin d) :
    suffixFinPermHom d q σ (Fin.castAdd q j) = Fin.castAdd q j := by
  exact Equiv.Perm.ofSubtype_apply_of_not_mem _ (by simp [j.isLt])

theorem finiteIsometryAverage_comp_mulEquiv {E G H : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] [Group G] [Fintype G] [Group H] [Fintype H]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (e : H ≃* G) (x : E) :
    finiteIsometryAverage (ρ.comp e.toMonoidHom) x = finiteIsometryAverage ρ x := by
  unfold finiteIsometryAverage
  rw [Fintype.card_congr e.toEquiv]
  congr 1
  exact Equiv.sum_comp e.toEquiv (fun g => ρ g x)

theorem finitePrefixSet_average {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {m p : ℕ} (h : m ≤ p) (ρ : Equiv.Perm (Fin p) →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    finiteIsometryAverage (ρ.comp (Equiv.Perm.ofSubtype : Equiv.Perm (finPrefixSet m p) →* Equiv.Perm (Fin p))) x =
      finiteIsometryAverage (ρ.comp (prefixFinPermHom h)) x := by
  have he : ((ρ.comp Equiv.Perm.ofSubtype).comp (finPrefixSetEquiv h).permCongrHom.toMonoidHom) =
      ρ.comp (prefixFinPermHom h) := by
    apply MonoidHom.ext
    intro σ
    change ρ (Equiv.Perm.ofSubtype ((finPrefixSetEquiv h).permCongrHom σ)) = _
    rw [ofSubtype_finPrefixSetEquiv]
    rfl
  rw [← he]
  exact (finiteIsometryAverage_comp_mulEquiv (ρ.comp Equiv.Perm.ofSubtype)
    (finPrefixSetEquiv h).permCongrHom x).symm

/-- The actual first-2d average in the BKL two-block inequality. Both symmetry
premises refer to literal coordinate subgroup actions. -/
theorem norm_le_four_pow_mul_prefixAverage {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (d q : ℕ) (hq : q = 2 * d)
    (ρ : Equiv.Perm (Fin (d + q)) →* (E ≃ₗᵢ[ℝ] E)) (x : E)
    (hA : ∀ σ : Equiv.Perm (Fin d), ρ (prefixFinPermHom (by omega : d ≤ d + q) σ) x = x)
    (hC : ∀ σ : Equiv.Perm (Fin q), ρ (suffixFinPermHom d q σ) x = x) :
    ‖x‖ ≤ (4 : ℝ) ^ d * ‖finiteIsometryAverage
      (ρ.comp (prefixFinPermHom (by omega : 2 * d ≤ d + q))) x‖ := by
  have hA' (σ : Equiv.Perm (finPrefixSet d (d + q))) : ρ (Equiv.Perm.ofSubtype σ) x = x := by
    obtain ⟨τ, rfl⟩ := (finPrefixSetEquiv (by omega : d ≤ d + q)).permCongrHom.surjective σ
    rw [ofSubtype_finPrefixSetEquiv]
    exact hA τ
  have hC' (σ : Equiv.Perm {i : Fin (d + q) // i ∉ finPrefixSet d (d + q)}) :
      ρ (Equiv.Perm.ofSubtype σ) x = x := by
    obtain ⟨τ, rfl⟩ := (finPrefixComplementEquiv d q).permCongrHom.surjective σ
    exact hC τ
  have hn := norm_le_four_pow_mul_blockAverage_of_two_block_symmetry ρ x Finset.univ
    (finPrefixSet d (d + q)) (finPrefixSet (2 * d) (d + q)) d
    (by simp; omega) (finPrefixSet_card (by omega)) (finPrefixSet_card (by omega))
    (finPrefixSet_mono (by omega)) (Finset.subset_univ _) hA' hC'
  rwa [finitePrefixSet_average (by omega)] at hn

end KLS
end

#print axioms KLS.finitePrefixSet_average
#print axioms KLS.norm_le_four_pow_mul_prefixAverage
