import KLS.TailSubsets
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Powerset

/-! The exact factorial cancellation in (105), with the energy index one
smaller than the cumulant order, and the labeled-subset multiplicity. -/
open scoped BigOperators
noncomputable section
namespace KLS

def cumulantEnergyMajorant (K : ℝ) (r : ℕ) : ℝ := K^r * (r.factorial : ℝ)^2

theorem cumulantEnergyMajorant_pos {K : ℝ} (hK : 0 < K) (r : ℕ) :
    0 < cumulantEnergyMajorant K r := by
  unfold cumulantEnergyMajorant
  positivity

theorem cumulantEnergyMajorant_succ (K : ℝ) (r : ℕ) :
    cumulantEnergyMajorant K (r+1) = K * ((r+1 : ℕ) : ℝ)^2 * cumulantEnergyMajorant K r := by
  simp only [cumulantEnergyMajorant, pow_succ, Nat.factorial_succ, Nat.cast_mul]
  ring

theorem cumulantEnergyMajorant_step (K : ℝ) {r : ℕ} (hr : 1 ≤ r) :
    cumulantEnergyMajorant K r = K * (r : ℝ)^2 * cumulantEnergyMajorant K (r-1) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  simpa only [Nat.add_one_sub_one] using cumulantEnergyMajorant_succ K j

theorem cumulantEnergyMajorant_choose {K : ℝ} (r j : ℕ) (hj : j ≤ r) :
    (r.choose j : ℝ)^2 * (cumulantEnergyMajorant K j * cumulantEnergyMajorant K (r-j)) =
      cumulantEnergyMajorant K r := by
  have hf : (r.choose j : ℝ) * (j.factorial : ℝ) * ((r-j).factorial : ℝ) = r.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hj
  unfold cumulantEnergyMajorant
  calc
    _ = (K^j * K^(r-j)) * ((r.choose j : ℝ) * (j.factorial : ℝ) * ((r-j).factorial : ℝ))^2 := by ring
    _ = _ := by rw [← pow_add, Nat.add_sub_of_le hj, hf]

def activeTailSubsets (r : ℕ) : Finset (Finset (Fin r)) :=
  Finset.univ.filter fun T => 1 ≤ T.card ∧ T.card ≤ r-2

@[simp] theorem mem_activeTailSubsets {r : ℕ} {T : Finset (Fin r)} :
    T ∈ activeTailSubsets r ↔ 1 ≤ T.card ∧ T.card ≤ r-2 := by simp [activeTailSubsets]

def subsetBinomialWeight {r : ℕ} (T : Finset (Fin r)) : ℝ := (r.choose T.card : ℝ)⁻¹

theorem subsetBinomialWeight_pos {r : ℕ} (T : Finset (Fin r)) :
    0 < subsetBinomialWeight T := by
  unfold subsetBinomialWeight
  exact inv_pos.mpr (by exact_mod_cast Nat.choose_pos (by simpa using T.card_le_univ))

theorem sum_subsetBinomialWeight (r : ℕ) :
    (∑ T ∈ activeTailSubsets r, subsetBinomialWeight T) = (r-2 : ℕ) := by
  have hmap (T : Finset (Fin r)) (hT : T ∈ activeTailSubsets r) :
      T.card ∈ Finset.Icc 1 (r-2) := by simpa using hT
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  have hf (j : ℕ) (hj : j ∈ Finset.Icc 1 (r-2)) :
      (activeTailSubsets r).filter (fun T => T.card = j) =
        (Finset.univ : Finset (Fin r)).powersetCard j := by
    ext T
    simp only [Finset.mem_filter, mem_activeTailSubsets, Finset.mem_powersetCard,
      Finset.subset_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨by simpa [h] using hj, h⟩
  calc
    _ = ∑ j ∈ Finset.Icc 1 (r-2), (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hf j hj]
      have he (T : Finset (Fin r)) (hT : T ∈ Finset.univ.powersetCard j) :
          subsetBinomialWeight T = (r.choose j : ℝ)⁻¹ := by
        rw [subsetBinomialWeight, (Finset.mem_powersetCard.mp hT).2]
      rw [Finset.sum_congr rfl he, Finset.sum_const, Finset.card_powersetCard]
      simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact mul_inv_cancel₀ (by exact_mod_cast (Nat.choose_pos (by have := Finset.mem_Icc.mp hj; omega)).ne')
    _ = _ := by simp

theorem majorant_div_weight_mul_lower (K : ℝ) {r : ℕ} (T : Finset (Fin r)) :
    (cumulantEnergyMajorant K Tᶜ.card / subsetBinomialWeight T) *
      (2 * cumulantEnergyMajorant K T.card) =
        2 * cumulantEnergyMajorant K r * subsetBinomialWeight T := by
  have hcard : T.card ≤ r := by simpa using T.card_le_univ
  have hcompl : Tᶜ.card = r-T.card := by rw [Finset.card_compl, Fintype.card_fin]
  have hc : (r.choose T.card : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hcard).ne'
  have he := cumulantEnergyMajorant_choose (K := K) r T.card hcard
  rw [← hcompl] at he
  unfold subsetBinomialWeight
  field_simp
  nlinarith [he]

end KLS
end
