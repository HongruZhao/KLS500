import KLS.WeightedWeakRegularity

/-!
# Local Lebesgue control and the actual distribution equation

A continuous finite potential gives quantitative comparison with Lebesgue
measure on each compact set. Consequently every weighted L² function is
locally in ordinary L². The weighted annihilator identity is then rewritten
as an unweighted distribution identity for the actual density and derivatives.
These results do not assert existence of weak first derivatives or regularity.
-/

open MeasureTheory InnerProductSpace Set Filter
open scoped ContDiff ENNReal

noncomputable section
namespace KLS

variable {n : ℕ}

/-- An upper bound for the potential gives an actual local measure comparison. -/
theorem restrict_volume_le_exp_smul_potentialMeasure {φ : Space n → ℝ}
    (hφ : Measurable φ) {K : Set (Space n)} (hK : MeasurableSet K)
    {M : ℝ} (hM : ∀ x ∈ K, φ x ≤ M) :
    volume.restrict K ≤ ENNReal.ofReal (Real.exp M) • potentialMeasure φ := by
  rw [← withDensity_indicator_one hK]
  unfold potentialMeasure
  have hm : Measurable (fun x => ENNReal.ofReal (Real.exp (-φ x))) := by fun_prop
  rw [← withDensity_smul _ hm]
  apply withDensity_mono
  apply Eventually.of_forall
  intro x
  by_cases hx : x ∈ K
  · simp only [Set.indicator_of_mem hx, Pi.one_apply, Pi.smul_apply, smul_eq_mul]
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    exact ENNReal.one_le_ofReal.mpr (Real.one_le_exp_iff.mpr (by linarith [hM x hx]))
  · simp [hx]

/-- Every compact set admits a finite comparison constant for the actual weighted measure. -/
theorem exists_restrict_volume_le_smul_potentialMeasure {φ : Space n → ℝ}
    (hφ : Continuous φ) {K : Set (Space n)} (hK : IsCompact K) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ volume.restrict K ≤ C • potentialMeasure φ := by
  obtain ⟨M, hM⟩ := hK.bddAbove_image hφ.continuousOn
  refine ⟨ENNReal.ofReal (Real.exp M), ENNReal.ofReal_ne_top, ?_⟩
  exact restrict_volume_le_exp_smul_potentialMeasure hφ.measurable hK.measurableSet
    (fun x hx => hM (mem_image_of_mem φ hx))

/-- Weighted Lᵖ membership implies ordinary Lᵖ membership on every compact set. -/
theorem MemLp.restrict_volume_of_potentialMeasure {φ f : Space n → ℝ} {p : ℝ≥0∞}
    (hf : MemLp f p (potentialMeasure φ)) (hφ : Continuous φ)
    {K : Set (Space n)} (hK : IsCompact K) : MemLp f p (volume.restrict K) := by
  obtain ⟨C, hC, hle⟩ := exists_restrict_volume_le_smul_potentialMeasure hφ hK
  exact (hf.smul_measure hC).mono_measure hle

/-- In particular, a weighted L² function is locally Lebesgue integrable. -/
theorem MemLp.locallyIntegrable_volume_of_potentialMeasure {φ f : Space n → ℝ}
    (hf : MemLp f 2 (potentialMeasure φ)) (hφ : Continuous φ) :
    LocallyIntegrable f volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  let : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  exact MeasureTheory.MemLp.integrable (q := 2) (by norm_num)
    (KLS.MemLp.restrict_volume_of_potentialMeasure hf hφ hK)

/-- The coordinate Laplacian of a compact C² test is itself continuous and compactly supported. -/
lemma memLp_coordinateLaplacian_of_hasCompactSupport {φ g : Space n → ℝ}
    (hφ : Continuous φ) (hg : ContDiff ℝ 2 g) (hc : HasCompactSupport g) :
    MemLp (coordinateLaplacian g) 2 (potentialMeasure φ) := by
  apply memLp_of_continuous_hasCompactSupport hφ
  · unfold coordinateLaplacian
    exact continuous_finsetSum _ (fun i _ =>
      (contDiff_coordinateHessian hg (m := 0) (by norm_num) i i).continuous)
  · have hsum := HasCompactSupport.finset_sum (s := Finset.univ)
      (fun i _ => hasCompactSupport_coordinateHessian hc i i)
    convert hsum using 1
    funext x
    simp [coordinateLaplacian, Finset.sum_apply]

/-- The density times the diffusion is exactly the divergence of the weighted gradient. -/
theorem exp_neg_mul_weightedDiffusion_eq_sum_derivative {φ g : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hg : ContDiff ℝ 2 g) (x : Space n) :
    Real.exp (-φ x) * weightedDiffusion φ g x =
      ∑ i, coordinateDerivative
        (fun y => Real.exp (-φ y) * coordinateDerivative g i y) i x := by
  rw [weightedDiffusion_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hφd := hφ.differentiable (by norm_num) x
  have hgd := (contDiff_coordinateDerivative hg (m := 1) (by norm_num) i).differentiable
    (by norm_num) x
  have hρd : DifferentiableAt ℝ (fun y => Real.exp (-φ y)) x := by
    simpa only [Pi.neg_apply] using hφd.neg.exp
  rw [coordinateDerivative_mul hρd hgd]
  change Real.exp (-φ x) *
      (coordinateHessian g x i i - coordinateDerivative g i x * coordinateDerivative φ i x) =
    fderiv ℝ (fun y => Real.exp (-φ y)) x (EuclideanSpace.single i 1) *
      coordinateDerivative g i x + Real.exp (-φ x) * coordinateHessian g x i i
  rw [fderiv_exp_neg_apply hφd]
  dsimp [coordinateDerivative]
  ring

/-- Weighted harmonic annihilation is the ordinary distribution equation
`∫ u div(exp(-φ) grad(g)) = 0`, with actual Fréchet derivatives. -/
theorem weak_diffusion_unweighted_divergence {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (u : Lp ℝ 2 (potentialMeasure φ))
    (hu : ∀ g : Space n → ℝ, ContDiff ℝ 3 g → HasCompactSupport g →
      (∫ x, u x * weightedDiffusion φ g x ∂potentialMeasure φ) = 0)
    {g : Space n → ℝ} (hg : ContDiff ℝ 3 g) (hc : HasCompactSupport g) :
    (∫ x, u x * ∑ i, coordinateDerivative
      (fun y => Real.exp (-φ y) * coordinateDerivative g i y) i x) = 0 := by
  have he := hu g hg hc
  rw [integral_potentialMeasure hφ.continuous.measurable] at he
  convert he using 1
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only
    rw [← exp_neg_mul_weightedDiffusion_eq_sum_derivative hφ (hg.of_le (by norm_num)) x]
    ring

/-- The unweighted distribution integrand is genuinely integrable for an L² function. -/
theorem integrable_unweighted_mul_divergence {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (u : Lp ℝ 2 (potentialMeasure φ))
    {g : Space n → ℝ} (hg : ContDiff ℝ 3 g) (hc : HasCompactSupport g) :
    Integrable (fun x => u x * ∑ i, coordinateDerivative
      (fun y => Real.exp (-φ y) * coordinateDerivative g i y) i x) volume := by
  have hi := (Lp.memLp u).integrable_mul
    (memLp_weightedDiffusion_of_hasCompactSupport hφ hg hc)
  have hi' := (integrable_potentialMeasure_iff hφ.continuous.measurable).mp hi
  convert hi' using 1
  funext x
  dsimp only [Pi.mul_apply]
  rw [← exp_neg_mul_weightedDiffusion_eq_sum_derivative
    (hφ.of_le (by norm_num)) (hg.of_le (by norm_num)) x]
  ring

/-- The same equation with its Laplacian and first-order terms separated.
The weighted L² bound and compact support justify both ordinary integrals. -/
theorem weak_diffusion_unweighted_laplacian {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (u : Lp ℝ 2 (potentialMeasure φ))
    (hu : ∀ g : Space n → ℝ, ContDiff ℝ 3 g → HasCompactSupport g →
      (∫ x, u x * weightedDiffusion φ g x ∂potentialMeasure φ) = 0)
    {g : Space n → ℝ} (hg : ContDiff ℝ 3 g) (hc : HasCompactSupport g) :
    (∫ x, u x * Real.exp (-φ x) * coordinateLaplacian g x) =
      ∫ x, u x * Real.exp (-φ x) * inner ℝ (gradient φ x) (gradient g x) := by
  have hIlap : Integrable (fun x => u x * coordinateLaplacian g x) (potentialMeasure φ) :=
    (Lp.memLp u).integrable_mul
      (memLp_coordinateLaplacian_of_hasCompactSupport hφ.continuous
        (hg.of_le (by norm_num)) hc)
  have hIdiff : Integrable (fun x => u x * weightedDiffusion φ g x) (potentialMeasure φ) :=
    (Lp.memLp u).integrable_mul
      (memLp_weightedDiffusion_of_hasCompactSupport hφ hg hc)
  have hIdrift : Integrable (fun x => u x * inner ℝ (gradient φ x) (gradient g x))
      (potentialMeasure φ) := by
    convert hIlap.sub hIdiff using 1
    funext x
    dsimp only [Pi.sub_apply, weightedDiffusion]
    ring
  have he := hu g hg hc
  have hsplit : (∫ x, u x * weightedDiffusion φ g x ∂potentialMeasure φ) =
      (∫ x, u x * coordinateLaplacian g x ∂potentialMeasure φ) -
        ∫ x, u x * inner ℝ (gradient φ x) (gradient g x) ∂potentialMeasure φ := by
    rw [← integral_sub hIlap hIdrift]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by dsimp [weightedDiffusion]; ring
  rw [hsplit, sub_eq_zero] at he
  rw [integral_potentialMeasure hφ.continuous.measurable,
    integral_potentialMeasure hφ.continuous.measurable] at he
  convert he using 1 <;> apply integral_congr_ae <;>
    exact Eventually.of_forall fun x => by dsimp only; ring

end KLS
end

#print axioms KLS.restrict_volume_le_exp_smul_potentialMeasure
#print axioms KLS.exists_restrict_volume_le_smul_potentialMeasure
#print axioms KLS.MemLp.restrict_volume_of_potentialMeasure
#print axioms KLS.exp_neg_mul_weightedDiffusion_eq_sum_derivative
#print axioms KLS.weak_diffusion_unweighted_divergence

#print axioms KLS.MemLp.locallyIntegrable_volume_of_potentialMeasure
#print axioms KLS.integrable_unweighted_mul_divergence
#print axioms KLS.weak_diffusion_unweighted_laplacian
