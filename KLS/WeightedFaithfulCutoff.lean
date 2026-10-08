import KLS.RealEndpoint
import KLS.SmoothCutoffSequence
import KLS.MollificationLocalization

/-! Actual compact cutoff approximation for every locally Lipschitz finite-energy test. -/

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal

noncomputable section
namespace KLS
variable {n : ℕ}

lemma measurable_coordinateDerivative (f : Space n → ℝ) (i : Fin n) :
    Measurable (coordinateDerivative f i) := by
  have h := (EuclideanSpace.proj i : Space n →L[ℝ] ℝ).continuous.measurable.comp
    (measurable_gradient f)
  have he : coordinateDerivative f i = fun x => (gradient f x) i :=
    funext (coordinateDerivative_eq_gradient f i)
  rw [he]
  exact h

lemma norm_coordinateDerivative_le (f : Space n → ℝ) (i : Fin n) (x : Space n) :
    ‖coordinateDerivative f i x‖ ≤ ‖gradient f x‖ := by
  rw [coordinateDerivative_eq_gradient]
  exact PiLp.norm_apply_le _ _

/-- Finite extended energy gives actual square-integrable coordinate derivatives. -/
theorem memLp_coordinateDerivative_of_energy_lt_top {μ : Measure (Space n)}
    {f : Space n → ℝ} (he : energy μ f < ⊤) (i : Fin n) :
    MemLp (coordinateDerivative f i) 2 μ := by
  have hg : MemLp (gradient f) 2 μ :=
    (memLp_two_iff_integrable_sq_norm (measurable_gradient f).aestronglyMeasurable).mpr
      (integrable_gradient_norm_sq_of_energy_lt_top he)
  exact hg.norm.mono' (measurable_coordinateDerivative f i).aestronglyMeasurable
    (Eventually.of_forall fun x => norm_coordinateDerivative_le f i x)

lemma faithfulCutoff_bounds (k : ℕ) (x : Space n) :
    0 ≤ smoothCutoff n k x ∧ smoothCutoff n k x ≤ 1 :=
  ⟨(unitCutoff n).nonneg, (unitCutoff n).le_one⟩

lemma smoothCutoff_coordinateDerivative_tendsto_zero (i : Fin n) (x : Space n) :
    Tendsto (fun k => coordinateDerivative (smoothCutoff n k) i x) atTop (𝓝 0) := by
  obtain ⟨K, hK, hb⟩ := smoothCutoff_gradient_bound (n := n)
  apply squeeze_zero_norm
    (fun k => (norm_coordinateDerivative_le _ i x).trans (hb k x))
  simpa using cutoffScale_tendsto_zero.mul_const K

lemma eLpNorm_eq_ofReal_sqrt_integral_sq {μ : Measure (Space n)}
    {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    eLpNorm f 2 μ = ENNReal.ofReal (Real.sqrt (∫ x, f x ^ 2 ∂μ)) := by
  rw [integral_sq_eq_toReal_eLpNorm_sq hf, Real.sqrt_sq ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal hf.eLpNorm_ne_top]

lemma tendsto_eLpNorm_zero_of_integral_sq {μ : Measure (Space n)}
    {f : ℕ → Space n → ℝ} (hf : ∀ k, MemLp (f k) 2 μ)
    (h : Tendsto (fun k => ∫ x, f k x ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (f k) 2 μ) atTop (𝓝 0) := by
  simp_rw [eLpNorm_eq_ofReal_sqrt_integral_sq (hf _)]
  have hs : Tendsto (fun k => Real.sqrt (∫ x, f k x ^ 2 ∂μ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp h
  simpa only [Function.comp_def, ENNReal.ofReal_zero] using (ENNReal.continuous_ofReal.tendsto 0).comp hs

/-- Actual smooth spatial cutoffs converge to every L² function in the same weighted L² norm. -/
theorem eLpNorm_smoothCutoff_mul_sub_tendsto_zero {μ : Measure (Space n)}
    {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    Tendsto (fun k => eLpNorm (fun x => smoothCutoff n k x * f x - f x) 2 μ)
      atTop (𝓝 0) := by
  have hm (k : ℕ) : AEStronglyMeasurable
      (fun x => smoothCutoff n k x * f x - f x) μ :=
    ((smoothCutoff_contDiff k).continuous.aestronglyMeasurable.mul hf.aestronglyMeasurable).sub
      hf.aestronglyMeasurable
  have hbound (k : ℕ) (x : Space n) :
      (smoothCutoff n k x * f x - f x) ^ 2 ≤ f x ^ 2 := by
    obtain ⟨h0, h1⟩ := faithfulCutoff_bounds k x
    have hsq : (smoothCutoff n k x - 1) ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hsq (sq_nonneg (f x))]
  have hmem (k : ℕ) : MemLp (fun x => smoothCutoff n k x * f x - f x) 2 μ :=
    (memLp_two_iff_integrable_sq (hm k)).mpr <|
      hf.integrable_sq.mono' ((hm k).pow 2)
        (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          exact hbound k x)
  apply tendsto_eLpNorm_zero_of_integral_sq hmem
  have h := tendsto_integral_of_dominated_convergence (fun x => f x ^ 2)
    (fun k => (hm k).pow 2) hf.integrable_sq
    (fun k => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hbound k x)
    (Eventually.of_forall fun x => by
      simpa using (((smoothCutoff_tendsto_one x).mul_const (f x)).sub_const (f x)).pow 2)
  simpa using h

lemma memLp_smoothCutoff_mul {μ : Measure (Space n)} {f : Space n → ℝ}
    (hf : MemLp f 2 μ) (k : ℕ) : MemLp (fun x => smoothCutoff n k x * f x) 2 μ := by
  have hχ : MemLp (smoothCutoff n k) ⊤ μ :=
    memLp_top_of_bound (smoothCutoff_contDiff k).continuous.aestronglyMeasurable 1
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (faithfulCutoff_bounds k x).1]
        exact (faithfulCutoff_bounds k x).2)
  exact hχ.mul hf

/-- The derivative of the actual cutoff product agrees almost everywhere with the classical product rule. -/
theorem coordinateDerivative_smoothCutoff_mul_ae {μ : Measure (Space n)}
    (hμ : μ ≪ volume) {f : Space n → ℝ} (hf : LocallyLipschitz f) (k : ℕ) (i : Fin n) :
    coordinateDerivative (fun x => smoothCutoff n k x * f x) i =ᵐ[μ]
      fun x => smoothCutoff n k x * coordinateDerivative f i x +
        coordinateDerivative (smoothCutoff n k) i x * f x := by
  filter_upwards [locallyLipschitz_ae_differentiableAt_of_absolutelyContinuous hμ hf] with x hx
  rw [coordinateDerivative_mul ((smoothCutoff_contDiff k).differentiable (by norm_num) x) hx]
  ring

/-- Compact cutoff derivatives are genuinely L², without smoothness of the input function. -/
theorem memLp_coordinateDerivative_smoothCutoff_mul {μ : Measure (Space n)}
    (hμ : μ ≪ volume) {f : Space n → ℝ} (hf : LocallyLipschitz f)
    (hf2 : MemLp f 2 μ) (he : energy μ f < ⊤) (k : ℕ) (i : Fin n) :
    MemLp (coordinateDerivative (fun x => smoothCutoff n k x * f x) i) 2 μ := by
  obtain ⟨K, _, hb⟩ := smoothCutoff_gradient_bound (n := n)
  have hχ : MemLp (coordinateDerivative (smoothCutoff n k) i) ⊤ μ :=
    memLp_top_of_bound (measurable_coordinateDerivative _ i).aestronglyMeasurable
      (cutoffScale k * K)
      (Eventually.of_forall fun x => (norm_coordinateDerivative_le _ i x).trans (hb k x))
  exact (memLp_congr_ae (coordinateDerivative_smoothCutoff_mul_ae hμ hf k i)).mpr
    ((memLp_smoothCutoff_mul (memLp_coordinateDerivative_of_energy_lt_top he i) k).add
      (hχ.mul hf2))

/-- Every coordinate derivative of a locally Lipschitz finite-energy test is approximated
strongly in its actual weighted L² norm by the corresponding compact cutoff derivatives. -/
theorem eLpNorm_smoothCutoff_derivative_sub_tendsto_zero {μ : Measure (Space n)}
    (hμ : μ ≪ volume) {f : Space n → ℝ} (hf : LocallyLipschitz f)
    (hf2 : MemLp f 2 μ) (he : energy μ f < ⊤) (i : Fin n) :
    Tendsto (fun k => eLpNorm
      (coordinateDerivative (fun x => smoothCutoff n k x * f x) i - coordinateDerivative f i) 2 μ)
      atTop (𝓝 0) := by
  let D := coordinateDerivative f i
  let F (k : ℕ) := coordinateDerivative (fun x => smoothCutoff n k x * f x) i - D
  have hD : MemLp D 2 μ := memLp_coordinateDerivative_of_energy_lt_top he i
  have hF (k : ℕ) : MemLp (F k) 2 μ :=
    (memLp_coordinateDerivative_smoothCutoff_mul hμ hf hf2 he k i).sub hD
  obtain ⟨K, hK, hb⟩ := smoothCutoff_gradient_bound (n := n)
  have hKu (k : ℕ) (x : Space n) : ‖coordinateDerivative (smoothCutoff n k) i x‖ ≤ K := by
    refine ((norm_coordinateDerivative_le _ i x).trans (hb k x)).trans ?_
    have hs : cutoffScale k ≤ 1 := by
      unfold cutoffScale
      apply inv_le_one_of_one_le₀
      linarith [Nat.cast_nonneg (α := ℝ) k]
    exact mul_le_of_le_one_left hK hs
  have heq (k : ℕ) : F k =ᵐ[μ] fun x =>
      (smoothCutoff n k x - 1) * D x + coordinateDerivative (smoothCutoff n k) i x * f x := by
    filter_upwards [coordinateDerivative_smoothCutoff_mul_ae hμ hf k i] with x hx
    dsimp [F, D] at *
    rw [hx]
    ring
  apply tendsto_eLpNorm_zero_of_integral_sq hF
  have hbnd (k : ℕ) : ∀ᵐ x ∂μ, ‖F k x ^ 2‖ ≤ 2 * D x ^ 2 + 2 * K ^ 2 * f x ^ 2 := by
    filter_upwards [heq k] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hx]
    have hχ := faithfulCutoff_bounds k x
    have hχsq : (smoothCutoff n k x - 1) ^ 2 ≤ 1 := by nlinarith
    have hdsq : coordinateDerivative (smoothCutoff n k) i x ^ 2 ≤ K ^ 2 := by
      have hd := hKu k x
      rw [Real.norm_eq_abs] at hd
      have hab := abs_le.mp hd
      nlinarith [sq_nonneg K, sq_nonneg (coordinateDerivative (smoothCutoff n k) i x)]
    nlinarith [sq_nonneg ((smoothCutoff n k x - 1) * D x -
      coordinateDerivative (smoothCutoff n k) i x * f x),
      mul_le_mul_of_nonneg_right hχsq (sq_nonneg (D x)),
      mul_le_mul_of_nonneg_right hdsq (sq_nonneg (f x))]
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun k => F k x ^ 2) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [ae_all_iff.mpr heq] with x hx
    have hl := (((smoothCutoff_tendsto_one x).sub_const 1).mul_const (D x)).add
      ((smoothCutoff_coordinateDerivative_tendsto_zero i x).mul_const (f x))
    simpa only [hx, sub_self, zero_mul, zero_add, zero_pow (by norm_num : 2 ≠ 0)] using hl.pow 2
  have ht := tendsto_integral_of_dominated_convergence
    (fun x => 2 * D x ^ 2 + 2 * K ^ 2 * f x ^ 2)
    (fun k => (hF k).aestronglyMeasurable.pow 2)
    ((hD.integrable_sq.const_mul 2).add (hf2.integrable_sq.const_mul (2 * K ^ 2))) hbnd hlim
  simpa only [integral_zero, Pi.pow_apply] using ht

/-- The concrete approximation keeps every original faithful test, with no new support or decay
hypothesis: its compact cutoff values and actual derivatives converge in weighted L². -/
theorem faithful_test_compact_cutoff_approximation {μ : Measure (Space n)}
    (hμ : μ ≪ volume) {f : Space n → ℝ} (hf : LocallyLipschitzTests μ f)
    (he : energy μ f < ⊤) :
    (∀ k, HasCompactSupport (fun x => smoothCutoff n k x * f x) ∧
      LocallyLipschitz (fun x => smoothCutoff n k x * f x) ∧
      MemLp (fun x => smoothCutoff n k x * f x) 2 μ ∧
      ∀ i : Fin n, MemLp (coordinateDerivative (fun x => smoothCutoff n k x * f x) i) 2 μ) ∧
    Tendsto (fun k => eLpNorm (fun x => smoothCutoff n k x * f x - f x) 2 μ) atTop (𝓝 0) ∧
    ∀ i : Fin n, Tendsto (fun k => eLpNorm
      (coordinateDerivative (fun x => smoothCutoff n k x * f x) i - coordinateDerivative f i) 2 μ)
      atTop (𝓝 0) := by
  exact ⟨fun k => ⟨(smoothCutoff_hasCompactSupport k).mul_right,
    ((show ContDiff ℝ 1 (fun p : ℝ × ℝ => p.1 * p.2) from
      contDiff_fst.mul contDiff_snd).locallyLipschitz.comp
        ((smoothCutoff_contDiff k).locallyLipschitz.prodMk hf.1)),
    memLp_smoothCutoff_mul hf.2 k,
    memLp_coordinateDerivative_smoothCutoff_mul hμ hf.1 hf.2 he k⟩,
    eLpNorm_smoothCutoff_mul_sub_tendsto_zero hf.2,
    eLpNorm_smoothCutoff_derivative_sub_tendsto_zero hμ hf.1 hf.2 he⟩

end KLS
end

#print axioms KLS.eLpNorm_smoothCutoff_mul_sub_tendsto_zero

#print axioms KLS.faithful_test_compact_cutoff_approximation
