import KLS.WeightedIterationBochner
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Corollary 3.5 for the actual normalized tensor iteration. Cumulative
Bochner dissipation proves summability and the zero-energy limit; finite
telescoping then gives the exact infinite sum of the actual mean losses. -/

open MeasureTheory InnerProductSpace Matrix Filter
open scoped ContDiff RealInnerProductSpace ENNReal Topology

noncomputable section
namespace KLS
variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

/-- The actual gradient-energy series is bounded by initial diffusion energy
divided by the actual positive curvature lower bound. -/
theorem weightedIterationEnergy_summable_and_bound
    {ι : Type*} [Fintype ι] (U : WeightedH1Family φ ι) (f : ι → Space n → ℝ)
    (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i))
    (hv : ∀ i, f i =ᵐ[volume] (weightedH1Value φ (U i) : Space n → ℝ))
    (hL : ∀ i, MemLp (weightedDiffusion φ (f i)) 2 (potentialMeasure φ)) :
    Summable (weightedIterationEnergy (hφ.of_le (by simp)) hκ hlower U) ∧
      (∑' k, weightedIterationEnergy (hφ.of_le (by simp)) hκ hlower U k) ≤
        (∑ i, ∫ x, weightedDiffusion φ (f i) x ^ 2 ∂potentialMeasure φ) / κ := by
  let hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by simp)
  obtain ⟨F, W, hzero, _, _, _, _, ht⟩ :=
    exists_weightedIteration_bochner_sequence hφ hκ hlower U f hf hv hL
  have hD0 : weightedIterationDiffusionEnergy φ F 0 =
      ∑ i, ∫ x, weightedDiffusion φ (f i) x ^ 2 ∂potentialMeasure φ := by
    change (∑ i : ι, ∫ x, weightedDiffusion φ (F 0 i) x ^ 2 ∂potentialMeasure φ) = _
    rw [hzero]
  have hb (N : ℕ) : (∑ k ∈ Finset.range N, weightedIterationEnergy hφ2 hκ hlower U k) ≤
      weightedIterationDiffusionEnergy φ F 0 / κ := by
    apply (le_div_iff₀ hκ).mpr
    have h := ht N
    have hD := weightedIterationDiffusionEnergy_nonneg φ F N
    have hC : 0 ≤ ∑ k ∈ Finset.range N, weightedIterationDefect hφ hκ hlower U W k :=
      Finset.sum_nonneg (fun k _ => weightedIterationDefect_nonneg hφ hκ hlower U W k)
    nlinarith
  refine ⟨summable_of_sum_range_le (weightedIterationEnergy_nonneg hφ2 hκ hlower U) hb, ?_⟩
  rw [← hD0]
  exact Real.tsum_le_of_sum_range_le (weightedIterationEnergy_nonneg hφ2 hκ hlower U) hb

/-- BKL Corollary 3.5: the gradient energy of the actual iterates tends to zero. -/
theorem weightedIterationEnergy_tendsto_zero
    {ι : Type*} [Fintype ι] (U : WeightedH1Family φ ι) (f : ι → Space n → ℝ)
    (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i))
    (hv : ∀ i, f i =ᵐ[volume] (weightedH1Value φ (U i) : Space n → ℝ))
    (hL : ∀ i, MemLp (weightedDiffusion φ (f i)) 2 (potentialMeasure φ)) :
    Tendsto (weightedIterationEnergy (hφ.of_le (by simp)) hκ hlower U) atTop (𝓝 0) :=
  (weightedIterationEnergy_summable_and_bound hφ hκ hlower U f hf hv hL).1.tendsto_atTop_zero

/-- The finite energy identity now passes to an actual infinite sum. -/
theorem weightedIterationMeanLoss_hasSum
    {ι : Type*} [Fintype ι] (U : WeightedH1Family φ ι) (f : ι → Space n → ℝ)
    (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i))
    (hv : ∀ i, f i =ᵐ[volume] (weightedH1Value φ (U i) : Space n → ℝ))
    (hL : ∀ i, MemLp (weightedDiffusion φ (f i)) 2 (potentialMeasure φ)) :
    HasSum (weightedIterationMeanLoss (hφ.of_le (by simp)) hκ hlower U)
      (‖weightedFamilyGradient φ ι U‖ ^ 2) := by
  let hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by simp)
  have he (N : ℕ) : (∑ k ∈ Finset.range N, weightedIterationMeanLoss hφ2 hκ hlower U k) =
      ‖weightedFamilyGradient φ ι U‖ ^ 2 - weightedIterationEnergy hφ2 hκ hlower U N := by
    have ht := weightedIterationEnergy_telescope hφ2 hκ hlower U N
    linarith
  have hb (N : ℕ) : (∑ k ∈ Finset.range N, weightedIterationMeanLoss hφ2 hκ hlower U k) ≤
      ‖weightedFamilyGradient φ ι U‖ ^ 2 := by
    rw [he]
    exact sub_le_self _ (weightedIterationEnergy_nonneg hφ2 hκ hlower U N)
  have hs := summable_of_sum_range_le (weightedIterationMeanLoss_nonneg hφ2 hκ hlower U) hb
  apply hs.hasSum_iff_tendsto_nat.mpr
  simp_rw [he]
  simpa only [sub_zero] using tendsto_const_nhds.sub
    (weightedIterationEnergy_tendsto_zero hφ hκ hlower U f hf hv hL)

/-- The actual Hessian defects are summable with total at most initial
diffusion energy. Their graph and classical interpretations are retained. -/
theorem exists_weightedIteration_summable_defects
    {ι : Type*} [Fintype ι] (U : WeightedH1Family φ ι) (f : ι → Space n → ℝ)
    (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i))
    (hv : ∀ i, f i =ᵐ[volume] (weightedH1Value φ (U i) : Space n → ℝ))
    (hL : ∀ i, MemLp (weightedDiffusion φ (f i)) 2 (potentialMeasure φ)) :
    ∃ (F : (k : ℕ) → WeightedIterationIndex n ι k → Space n → ℝ)
      (W : (k : ℕ) → WeightedH1Family φ (Fin n × WeightedIterationIndex n ι k)),
      F 0 = f ∧
      (∀ k i, ContDiff ℝ (⊤ : ℕ∞) (F k i)) ∧
      (∀ k i, F k i =ᵐ[volume] (weightedH1Value φ
        (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k i) : Space n → ℝ)) ∧
      (∀ k i, MemLp (weightedDiffusion φ (F k i)) 2 (potentialMeasure φ)) ∧
      (∀ k,
        weightedFamilyValue φ (Fin n × WeightedIterationIndex n ι k) (W k) =
          weightedFamilyCenteredGradient φ (WeightedIterationIndex n ι k)
            (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k) ∧
        ∀ j l i, (weightedH1Derivative φ j (W k (l, i)) : Space n → ℝ)
          =ᵐ[potentialMeasure φ] fun x => coordinateHessian (F k i) x j l) ∧
      Summable (weightedIterationDefect hφ hκ hlower U W) ∧
      (∑' k, weightedIterationDefect hφ hκ hlower U W k) ≤
        ∑ i, ∫ x, weightedDiffusion φ (f i) x ^ 2 ∂potentialMeasure φ := by
  let hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by simp)
  obtain ⟨F, W, hzero, hF, hV, hLF, hstep, ht⟩ :=
    exists_weightedIteration_bochner_sequence hφ hκ hlower U f hf hv hL
  have hD0 : weightedIterationDiffusionEnergy φ F 0 =
      ∑ i, ∫ x, weightedDiffusion φ (f i) x ^ 2 ∂potentialMeasure φ := by
    change (∑ i : ι, ∫ x, weightedDiffusion φ (F 0 i) x ^ 2 ∂potentialMeasure φ) = _
    rw [hzero]
  have hb (N : ℕ) : (∑ k ∈ Finset.range N, weightedIterationDefect hφ hκ hlower U W k) ≤
      weightedIterationDiffusionEnergy φ F 0 := by
    have h := ht N
    have hD := weightedIterationDiffusionEnergy_nonneg φ F N
    have hE : 0 ≤ ∑ k ∈ Finset.range N, weightedIterationEnergy hφ2 hκ hlower U k :=
      Finset.sum_nonneg (fun k _ => weightedIterationEnergy_nonneg hφ2 hκ hlower U k)
    have hκE := mul_nonneg hκ.le hE
    linarith
  refine ⟨F, W, hzero, hF, hV, hLF, fun k => ⟨(hstep k).1, (hstep k).2.1⟩,
    summable_of_sum_range_le (weightedIterationDefect_nonneg hφ hκ hlower U W) hb, ?_⟩
  rw [← hD0]
  exact Real.tsum_le_of_sum_range_le (weightedIterationDefect_nonneg hφ hκ hlower U W) hb

end KLS
end

#print axioms KLS.weightedIterationEnergy_summable_and_bound
#print axioms KLS.weightedIterationEnergy_tendsto_zero
#print axioms KLS.weightedIterationMeanLoss_hasSum
#print axioms KLS.exists_weightedIteration_summable_defects
