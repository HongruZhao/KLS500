import KLS.GlobalDampingWhiteningMoments
import KLS.PoincareWeakMeasureLimit

/-! Compact continuous tests converge for the actual damped and whitened laws. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped Topology ENNReal NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

lemma tendsto_affineMatrixMap_of_coefficients
    {A : ℕ → Matrix (Fin n) (Fin n) ℝ} {b : ℕ → Space n}
    (hlim : ∀ i j, Tendsto (fun k => affineCoordinateCoefficient (A k) (b k) i j)
      atTop (𝓝 (affineCoordinateCoefficient 1 0 i j))) (x : Space n) :
    Tendsto (fun k => affineMatrixMap (A k) (b k) x) atTop (𝓝 x) := by
  have hp : Tendsto (fun k => fun i => affineMatrixMap (A k) (b k) x i)
      atTop (𝓝 (fun i => x i)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    have hh := tendsto_finsetSum Finset.univ fun j _ => (hlim i j).mul_const (coordinateWithConstant j x)
    have hid : affineMatrixMap (1 : Matrix (Fin n) (Fin n) ℝ) 0 x = x := by
      ext j
      simp [affineMatrixMap_apply, matrixAction_apply, Matrix.one_apply]
    simpa only [← affineMatrixMap_coordinate_sum, hid] using hh
  simpa only [Function.comp_def, WithLp.toLp_ofLp] using
    (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).continuousAt.tendsto.comp hp

theorem tendsto_integral_affine_quadraticDamping_nonneg
    (μ : Measure (Space n)) [IsProbabilityMeasure μ]
    {ε : ℕ → ℝ} (hε : ∀ k, 0 ≤ ε k) (hεlim : Tendsto ε atTop (𝓝 0))
    {A : ℕ → Matrix (Fin n) (Fin n) ℝ} {b : ℕ → Space n}
    (hcoeff : ∀ i j, Tendsto (fun k => affineCoordinateCoefficient (A k) (b k) i j)
      atTop (𝓝 (affineCoordinateCoefficient 1 0 i j)))
    {f : Space n → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) :
    Tendsto (fun k => ∫ x, f x ∂affineMatrixMeasure (quadraticDamping μ (ε k)) (A k) (b k))
      atTop (𝓝 (∫ x, f x ∂μ)) := by
  obtain ⟨B, hB⟩ := (hc.isCompact_range hf).isBounded.exists_norm_le
  have hb (x : Space n) : ‖f x‖ ≤ B := hB (f x) (mem_range_self x)
  have ht := tendsto_integral_of_dominated_convergence (fun _ : Space n => B)
    (F := fun k x => f (affineMatrixMap (A k) (b k) x) * Real.exp (-ε k * ‖x‖ ^ 2))
    (f := f) (μ := μ) (fun _ => by fun_prop) (integrable_const _)
    (fun k => Eventually.of_forall fun x => by
      simp only [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact (mul_le_of_le_one_right (abs_nonneg _) (exp_quadraticDamping_le_one (hε k) x)).trans (hb _))
    (Eventually.of_forall fun x => by
      have he := (Real.continuous_exp.tendsto 0).comp
        (by simpa using hεlim.neg.mul_const (‖x‖ ^ 2))
      have hfx := hf.continuousAt.tendsto.comp (tendsto_affineMatrixMap_of_coefficients hcoeff x)
      simpa only [Real.exp_zero, mul_one, neg_mul, Function.comp_def] using hfx.mul he)
  have hden : Tendsto (fun k => tiltPartition μ (fun x => -ε k * ‖x‖ ^ 2)) atTop (𝓝 1) := by
    have h := tendsto_integral_of_dominated_convergence (fun _ : Space n => (1 : ℝ))
      (F := fun k x => Real.exp (-ε k * ‖x‖ ^ 2)) (f := fun _ => (1 : ℝ)) (μ := μ)
      (fun _ => by fun_prop) (integrable_const _)
      (fun k => Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using exp_quadraticDamping_le_one (hε k) x)
      (Eventually.of_forall fun x => by
        simpa only [Real.exp_zero, Function.comp_def, neg_mul] using
          (Real.continuous_exp.tendsto 0).comp (by simpa using hεlim.neg.mul_const (‖x‖ ^ 2)))
    simpa only [tiltPartition, integral_const, probReal_univ, one_smul] using h
  have he (k : ℕ) : (∫ x, f x ∂affineMatrixMeasure (quadraticDamping μ (ε k)) (A k) (b k)) =
      (∫ x, f (affineMatrixMap (A k) (b k) x) * Real.exp (-ε k * ‖x‖ ^ 2) ∂μ) /
        tiltPartition μ (fun x => -ε k * ‖x‖ ^ 2) := by
    rw [affineMatrixMeasure, integral_map (by fun_prop) hf.aestronglyMeasurable]
    exact tiltAverage_eq_ratio μ _ _
  simp_rw [he]
  simpa only [Pi.div_def, div_one] using ht.div hden one_ne_zero

theorem admissibleMeasure.tendsto_integral_whitened_quadraticDamping_compact
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {ε : ℕ → ℝ} (hε : ∀ k, 0 ≤ ε k) (hεlim : Tendsto ε atTop (𝓝 0))
    {f : Space n → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) :
    Tendsto (fun k => ∫ x, f x ∂whitenedMeasure (quadraticDamping μ (ε k)))
      atTop (𝓝 (∫ x, f x ∂μ)) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  exact tendsto_integral_affine_quadraticDamping_nonneg μ hε hεlim
    (tendsto_whitening_coefficient_quadraticDamping_nonneg hμ hε hεlim) hf hc

end KLS
end
