import KLS.WeightedIterationSmoothDomain

/-! Actual Bochner data and finite cumulative dissipation along the literal
normalized tensor iteration. The Hessian graph at each step is constructed
from its proved smooth diffusion-domain representative. -/

open MeasureTheory InnerProductSpace Matrix Filter
open scoped ContDiff RealInnerProductSpace ENNReal

noncomputable section
namespace KLS
variable {n : ℕ}

def weightedIterationDiffusionEnergy (φ : Space n → ℝ)
    {ι : Type*} [Fintype ι]
    (F : (k : ℕ) → WeightedIterationIndex n ι k → Space n → ℝ) (k : ℕ) : ℝ :=
  ∑ i : WeightedIterationIndex n ι k, ∫ x, weightedDiffusion φ (F k i) x ^ 2 ∂potentialMeasure φ

theorem weightedIterationDiffusionEnergy_nonneg (φ : Space n → ℝ)
    {ι : Type*} [Fintype ι]
    (F : (k : ℕ) → WeightedIterationIndex n ι k → Space n → ℝ) (k : ℕ) :
    0 ≤ weightedIterationDiffusionEnergy φ F k :=
  Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))

variable {φ : Space n → ℝ} {κ : ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

def weightedIterationDefect {ι : Type*} [Fintype ι] (U : WeightedH1Family φ ι)
    (W : (k : ℕ) → WeightedH1Family φ (Fin n × WeightedIterationIndex n ι k)) (k : ℕ) : ℝ :=
  weightedSuccessorHessianDefect (hφ.of_le (by simp)) hκ hlower
    (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k) (W k)

theorem weightedIterationDefect_nonneg {ι : Type*} [Fintype ι] (U : WeightedH1Family φ ι)
    (W : (k : ℕ) → WeightedH1Family φ (Fin n × WeightedIterationIndex n ι k)) (k : ℕ) :
    0 ≤ weightedIterationDefect hφ hκ hlower U W k := sq_nonneg _

/-- Construct the actual smooth and Hessian sequences and sum their proved
Bochner dissipation inequalities. No sequence equation or decay is an input. -/
theorem exists_weightedIteration_bochner_sequence
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
        (∀ j l i, (weightedH1Derivative φ j (W k (l, i)) : Space n → ℝ)
          =ᵐ[potentialMeasure φ] fun x => coordinateHessian (F k i) x j l) ∧
        (∑ i, ∫ x, hessianSquare (F k i) x ∂potentialMeasure φ) =
          weightedIterationDiffusionEnergy φ F (k + 1) + weightedIterationDefect hφ hκ hlower U W k ∧
        weightedIterationDiffusionEnergy φ F (k + 1) + weightedIterationDefect hφ hκ hlower U W k +
          κ * weightedIterationEnergy (hφ.of_le (by simp)) hκ hlower U k ≤
            weightedIterationDiffusionEnergy φ F k) ∧
      ∀ N : ℕ,
        weightedIterationDiffusionEnergy φ F N +
          (∑ k ∈ Finset.range N, weightedIterationDefect hφ hκ hlower U W k) +
          κ * (∑ k ∈ Finset.range N, weightedIterationEnergy (hφ.of_le (by simp)) hκ hlower U k) ≤
            weightedIterationDiffusionEnergy φ F 0 := by
  let hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by simp)
  obtain ⟨F, hzero, hF, hV, hLF⟩ :=
    exists_weightedIteration_smooth_representatives hφ hκ hlower U f hf hv hL
  have hs (k : ℕ) : ∃ V : WeightedH1Family φ (Fin n × WeightedIterationIndex n ι k),
      weightedFamilyValue φ (Fin n × WeightedIterationIndex n ι k) V =
        weightedFamilyCenteredGradient φ (WeightedIterationIndex n ι k)
          (weightedSuccessorIterate hφ2 hκ hlower U k) ∧
      (∀ j l i, (weightedH1Derivative φ j (V (l, i)) : Space n → ℝ)
        =ᵐ[potentialMeasure φ] fun x => coordinateHessian (F k i) x j l) ∧
      (∑ i, ∫ x, hessianSquare (F k i) x ∂potentialMeasure φ) =
        weightedIterationDiffusionEnergy φ F (k + 1) +
          weightedSuccessorHessianDefect hφ2 hκ hlower (weightedSuccessorIterate hφ2 hκ hlower U k) V ∧
      weightedIterationDiffusionEnergy φ F (k + 1) +
        weightedSuccessorHessianDefect hφ2 hκ hlower (weightedSuccessorIterate hφ2 hκ hlower U k) V +
        κ * weightedIterationEnergy hφ2 hκ hlower U k ≤ weightedIterationDiffusionEnergy φ F k := by
    obtain ⟨gnext, V, hg, hVV, hVD, _, hH, hB⟩ := exists_weightedNormalizedSuccessor_bochner_step
      hφ hκ hlower (weightedSuccessorIterate hφ2 hκ hlower U k) (F k) (hF k) (hV k) (hLF k)
    have he : gnext = F (k + 1) := by
      funext i
      exact continuous_representative_unique (hg i).1.continuous (hF (k + 1) i).continuous
        ((hg i).2.2.2.1.trans (hV (k + 1) i).symm)
    rw [he] at hH hB
    exact ⟨V, hVV, hVD, hH, hB⟩
  choose W hWV hWD hH hB using hs
  have ht (N : ℕ) : weightedIterationDiffusionEnergy φ F N +
      (∑ k ∈ Finset.range N, weightedIterationDefect hφ hκ hlower U W k) +
      κ * (∑ k ∈ Finset.range N, weightedIterationEnergy hφ2 hκ hlower U k) ≤
        weightedIterationDiffusionEnergy φ F 0 := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hb := hB N
      change weightedIterationDiffusionEnergy φ F (N + 1) +
        weightedIterationDefect hφ hκ hlower U W N + κ * weightedIterationEnergy hφ2 hκ hlower U N ≤
          weightedIterationDiffusionEnergy φ F N at hb
      nlinarith
  exact ⟨F, W, hzero, hF, hV, hLF, fun k => ⟨hWV k, hWD k, hH k, hB k⟩, ht⟩

end KLS
end

#print axioms KLS.exists_weightedIteration_bochner_sequence
