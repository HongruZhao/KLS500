import KLS.WeightedBochnerBounds

/-! Global Hessian and curvature integrability from the actual weighted diffusion domain. -/

open MeasureTheory InnerProductSpace Filter Matrix
open scoped BigOperators ContDiff ENNReal Topology

noncomputable section
set_option maxHeartbeats 800000
namespace KLS
variable {n : ℕ}

/-- Fatou's lemma turns uniform bounds for the concrete expanding cutoffs into global L¹. -/
theorem integrable_of_smoothCutoff_integrals_bounded {μ : Measure (Space n)}
    {F : Space n → ℝ} {B : ℝ} (hF : Continuous F) (h0 : ∀ x, 0 ≤ F x)
    (hI : ∀ k, Integrable (fun x => smoothCutoff n k x ^ 2 * F x) μ)
    (hB : ∀ k, (∫ x, smoothCutoff n k x ^ 2 * F x ∂μ) ≤ B) :
    Integrable F μ := by
  let G : ℕ → Space n → ℝ≥0∞ := fun k x => ENNReal.ofReal (smoothCutoff n k x ^ 2 * F x)
  have hm (k : ℕ) : Measurable (G k) :=
    (((smoothCutoff_contDiff k).continuous.pow 2).mul hF).measurable.ennreal_ofReal
  have ht (x : Space n) : Tendsto (fun k => G k x) atTop (𝓝 (ENNReal.ofReal (F x))) := by
    simpa only [G, one_pow, one_mul] using ENNReal.tendsto_ofReal
      (((smoothCutoff_tendsto_one x).pow 2).mul_const (F x))
  have hu (k : ℕ) : (∫⁻ x, G k x ∂μ) ≤ ENNReal.ofReal B := by
    have he := ofReal_integral_eq_lintegral_ofReal (hI k)
      (Eventually.of_forall fun x => mul_nonneg (sq_nonneg _) (h0 x))
    change (∫⁻ x, ENNReal.ofReal (smoothCutoff n k x ^ 2 * F x) ∂μ) ≤ _
    rw [← he]
    exact ENNReal.ofReal_le_ofReal (hB k)
  have hf := lintegral_liminf_le (μ := μ) (u := atTop) hm
  have he : (fun x => liminf (fun k => G k x) atTop) = fun x => ENNReal.ofReal (F x) :=
    funext fun x => (ht x).liminf_eq
  rw [he] at hf
  have hlim : liminf (fun k => ∫⁻ x, G k x ∂μ) atTop ≤ ENNReal.ofReal B :=
    liminf_le_of_frequently_le' (Eventually.frequently (Eventually.of_forall hu))
  exact (lintegral_ofReal_ne_top_iff_integrable hF.aestronglyMeasurable
    (Eventually.of_forall h0)).mp (lt_of_le_of_lt (hf.trans hlim) ENNReal.ofReal_lt_top).ne

/-- Global integrability of both nonnegative Bochner terms follows from the actual L²
diffusion and gradient, without compact support, polynomial growth, or a Bochner-domain premise. -/
theorem integrable_bochner_terms_of_diffusion_domain {φ f : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hf : ContDiff ℝ 3 f)
    (hcurv : ∀ x, 0 ≤ hessianGradientForm φ f x)
    (hL : MemLp (weightedDiffusion φ f) 2 (potentialMeasure φ))
    (hG : Integrable (fun x => ‖gradient f x‖ ^ 2) (potentialMeasure φ)) :
    Integrable (hessianSquare f) (potentialMeasure φ) ∧
      Integrable (hessianGradientForm φ f) (potentialMeasure φ) := by
  obtain ⟨K, hK, hbound⟩ := smoothCutoff_gradient_bound (n := n)
  have hKu (k : ℕ) (x : Space n) : ‖gradient (smoothCutoff n k) x‖ ≤ K := by
    apply (hbound k x).trans
    have hs : cutoffScale k ≤ 1 := by
      unfold cutoffScale
      apply inv_le_one_of_one_le₀
      linarith [Nat.cast_nonneg (α := ℝ) k]
    exact mul_le_of_le_one_left hK hs
  let S : Space n → ℝ := fun x => hessianSquare f x + hessianGradientForm φ f x
  have hSc : Continuous S :=
    (continuous_hessianSquare (hf.of_le (by norm_num))).add
      (continuous_hessianGradientForm hφ (hf.of_le (by norm_num)))
  have hS0 (x : Space n) : 0 ≤ S x := add_nonneg (hessianSquare_nonneg _ _) (hcurv x)
  have hI (k : ℕ) : Integrable (fun x => smoothCutoff n k x ^ 2 * S x) (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      (((smoothCutoff_contDiff k).continuous.pow 2).mul hSc)
      (by simpa only [pow_two, Pi.mul_def] using
        (smoothCutoff_hasCompactSupport (n := n) k).mul_right.mul_right (f' := S))
  have hB (k : ℕ) : (∫ x, smoothCutoff n k x ^ 2 * S x ∂potentialMeasure φ) ≤
      4 * (∫ x, weightedDiffusion φ f x ^ 2 ∂potentialMeasure φ) +
        6 * K ^ 2 * (∫ x, ‖gradient f x‖ ^ 2 ∂potentialMeasure φ) :=
    integral_cutoff_bochnerDensity_le hφ hf (smoothCutoff_contDiff k)
      (smoothCutoff_hasCompactSupport k) (fun x => (faithfulCutoff_bounds k x).1)
      (fun x => (faithfulCutoff_bounds k x).2) hK (hKu k) hcurv hL hG
  have hS := integrable_of_smoothCutoff_integrals_bounded hSc hS0 hI hB
  refine ⟨hS.mono' (continuous_hessianSquare (hf.of_le (by norm_num))).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_),
    hS.mono' (continuous_hessianGradientForm hφ (hf.of_le (by norm_num))).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)⟩
  · rw [Real.norm_eq_abs, abs_of_nonneg (hessianSquare_nonneg _ _)]
    exact le_add_of_nonneg_right (hcurv x)
  · rw [Real.norm_eq_abs, abs_of_nonneg (hcurv x)]
    exact le_add_of_nonneg_left (hessianSquare_nonneg _ _)

/-- The derived Hessian integrability is genuine weighted L² of every second derivative. -/
theorem memLp_coordinateHessian_of_integrable_hessianSquare {φ f : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (hH : Integrable (hessianSquare f) (potentialMeasure φ))
    (i j : Fin n) : MemLp (fun x => coordinateHessian f x i j) 2 (potentialMeasure φ) := by
  apply (memLp_two_iff_integrable_sq
    (contDiff_coordinateHessian hf (m := 0) (by norm_num) i j).continuous.aestronglyMeasurable).mpr
  apply hH.mono'
    ((contDiff_coordinateHessian hf (m := 0) (by norm_num) i j).continuous.pow 2).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact (Finset.single_le_sum (fun k _ => sq_nonneg (coordinateHessian f x i k))
    (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun l _ => sq_nonneg (coordinateHessian f x k l))
      (Finset.mem_univ i))

/-- The expanding cutoff integrals converge for every nonnegative integrable function. -/
theorem integral_smoothCutoff_sq_tendsto {μ : Measure (Space n)} {F : Space n → ℝ}
    (hF : Integrable F μ) (h0 : ∀ x, 0 ≤ F x) :
    Tendsto (fun k => ∫ x, smoothCutoff n k x ^ 2 * F x ∂μ) atTop (𝓝 (∫ x, F x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence F
    (fun k => ((smoothCutoff_contDiff k).continuous.pow 2).aestronglyMeasurable.mul hF.aestronglyMeasurable)
    hF
  · intro k
    filter_upwards [] with x
    simp only [Pi.mul_apply, Pi.pow_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (h0 x))]
    have hb := faithfulCutoff_bounds k x
    exact mul_le_of_le_one_left (h0 x) (by nlinarith)
  · filter_upwards [] with x
    simpa only [one_pow, one_mul, Pi.mul_apply, Pi.pow_apply] using ((smoothCutoff_tendsto_one x).pow 2).mul_const (F x)

/-- A vanishing scalar bound controls the integral of an actual error term. -/
theorem tendsto_integral_zero_of_vanishing_bound {μ : Measure (Space n)}
    {F : ℕ → Space n → ℝ} {W : Space n → ℝ} {c : ℕ → ℝ}
    (hW : Integrable W μ) (hc : Tendsto c atTop (𝓝 0))
    (hb : ∀ k x, |F k x| ≤ c k * W x) :
    Tendsto (fun k => ∫ x, F k x ∂μ) atTop (𝓝 0) := by
  apply squeeze_zero_norm
    (fun k => ?_) (by simpa using hc.mul_const (∫ x, W x ∂μ))
  calc
    _ ≤ ∫ x, c k * W x ∂μ := norm_integral_le_of_norm_le (hW.const_mul (c k))
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb k x)
    _ = _ := integral_const_mul _ _

/-- The sharp integrated Bochner identity holds throughout the actual smooth L² diffusion
and gradient domain. The integrability of its Hessian and curvature terms is derived above. -/
theorem integral_weightedDiffusion_sq_of_L2_domain {φ f : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hf : ContDiff ℝ 3 f)
    (hcurv : ∀ x, 0 ≤ hessianGradientForm φ f x)
    (hL : MemLp (weightedDiffusion φ f) 2 (potentialMeasure φ))
    (hG : Integrable (fun x => ‖gradient f x‖ ^ 2) (potentialMeasure φ)) :
    (∫ x, weightedDiffusion φ f x ^ 2 ∂potentialMeasure φ) =
      (∫ x, hessianSquare f x ∂potentialMeasure φ) +
        ∫ x, hessianGradientForm φ f x ∂potentialMeasure φ := by
  obtain ⟨hH, hC⟩ := integrable_bochner_terms_of_diffusion_domain hφ hf hcurv hL hG
  obtain ⟨K, hK, hbound⟩ := smoothCutoff_gradient_bound (n := n)
  let c : ℕ → ℝ := fun k => cutoffScale k * K
  have hc0 (k : ℕ) : 0 ≤ c k := mul_nonneg (cutoffScale_pos k).le hK
  have hct : Tendsto c atTop (𝓝 0) := by simpa [c] using cutoffScale_tendsto_zero.mul_const K
  have hχsq (k : ℕ) (x : Space n) : smoothCutoff n k x ^ 2 ≤ 1 := by
    have hb := faithfulCutoff_bounds k x
    nlinarith
  let B : ℕ → Space n → ℝ := fun k => bochnerCutoffError (fun x => smoothCutoff n k x ^ 2) f
  have hb (k : ℕ) (x : Space n) : |B k x| ≤ c k * (hessianSquare f x + ‖gradient f x‖ ^ 2) := by
    apply (abs_bochnerCutoffError_sq_le_vanishing
      ((smoothCutoff_contDiff k).differentiable (by norm_num)) x).trans
    exact mul_le_mul (hbound k x)
      (add_le_add (mul_le_of_le_one_left (hessianSquare_nonneg _ _) (hχsq k x)) le_rfl)
      (add_nonneg (mul_nonneg (sq_nonneg _) (hessianSquare_nonneg _ _)) (sq_nonneg _)) (hc0 k)
  have hBt : Tendsto (fun k => ∫ x, B k x ∂potentialMeasure φ) atTop (𝓝 0) :=
    tendsto_integral_zero_of_vanishing_bound (hH.add hG) hct hb
  let D : ℕ → Space n → ℝ := fun k x => weightedDiffusion φ f x *
    inner ℝ (gradient (fun y => smoothCutoff n k y ^ 2) x) (gradient f x)
  have hd (k : ℕ) (x : Space n) : |D k x| ≤ c k *
      (‖gradient f x‖ ^ 2 + weightedDiffusion φ f x ^ 2) := by
    apply (abs_cutoff_diffusion_error_le_vanishing
      ((smoothCutoff_contDiff k).differentiable (by norm_num)) x).trans
    exact mul_le_mul (hbound k x)
      (add_le_add (mul_le_of_le_one_left (sq_nonneg _) (hχsq k x)) le_rfl)
      (add_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)) (hc0 k)
  have hDt : Tendsto (fun k => ∫ x, D k x ∂potentialMeasure φ) atTop (𝓝 0) :=
    tendsto_integral_zero_of_vanishing_bound (hG.add hL.integrable_sq) hct hd
  have hLt := integral_smoothCutoff_sq_tendsto hL.integrable_sq (fun x => sq_nonneg (weightedDiffusion φ f x))
  have hSt := integral_smoothCutoff_sq_tendsto (hH.add hC)
    (fun x => add_nonneg (hessianSquare_nonneg f x) (hcurv x))
  have he (k : ℕ) := integral_localized_bochner_diffusion hφ hf
    ((smoothCutoff_contDiff k).pow 2)
    (show HasCompactSupport (fun x => smoothCutoff n k x ^ 2) from by
      simpa only [pow_two, Pi.mul_def] using
        (smoothCutoff_hasCompactSupport (n := n) k).mul_right (f' := smoothCutoff n k))
  have hrt : Tendsto
      (fun k => ∫ x, smoothCutoff n k x ^ 2 * (hessianSquare f x + hessianGradientForm φ f x)
        ∂potentialMeasure φ) atTop (𝓝 (∫ x, weightedDiffusion φ f x ^ 2 ∂potentialMeasure φ)) := by
    have ht := (hLt.add hDt).sub hBt
    simpa only [D, B, add_zero, sub_zero, ← he] using ht
  have hlim := tendsto_nhds_unique hSt hrt
  simp only [Pi.add_apply] at hlim
  rw [integral_add hH hC] at hlim
  exact hlim.symm

lemma hessianGradientForm_lower_bound {φ f : Space n → ℝ} {κ : ℝ}
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a)) (x : Space n) :
    κ * ‖gradient f x‖ ^ 2 ≤ hessianGradientForm φ f x := by
  have h := hlower x (fun i => coordinateDerivative f i x)
  have hg : (fun i => coordinateDerivative f i x) ⬝ᵥ (fun i => coordinateDerivative f i x) =
      ‖gradient f x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [dotProduct, coordinateDerivative_eq_gradient, pow_two]
  have he : (fun i => coordinateDerivative f i x) ⬝ᵥ
      (coordinateHessian φ x *ᵥ (fun i => coordinateDerivative f i x)) = hessianGradientForm φ f x := by
    simp only [dotProduct, Matrix.mulVec, hessianGradientForm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rwa [hg, he] at h

/-- Sharp lower-curvature Bochner estimate on the derived global diffusion domain. -/
theorem integral_hessianSquare_add_curvature_gradient_le_diffusion_sq
    {φ f : Space n → ℝ} {κ : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hf : ContDiff ℝ 3 f) (hκ : 0 ≤ κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (hL : MemLp (weightedDiffusion φ f) 2 (potentialMeasure φ))
    (hG : Integrable (fun x => ‖gradient f x‖ ^ 2) (potentialMeasure φ)) :
    (∫ x, hessianSquare f x ∂potentialMeasure φ) +
      κ * (∫ x, ‖gradient f x‖ ^ 2 ∂potentialMeasure φ) ≤
        ∫ x, weightedDiffusion φ f x ^ 2 ∂potentialMeasure φ := by
  have hl (x : Space n) := hessianGradientForm_lower_bound (f := f) hlower x
  have hc (x : Space n) : 0 ≤ hessianGradientForm φ f x :=
    (mul_nonneg hκ (sq_nonneg _)).trans (hl x)
  have hI := (integrable_bochner_terms_of_diffusion_domain hφ hf hc hL hG).2
  have hb := integral_mono (hG.const_mul κ) hI hl
  rw [integral_const_mul] at hb
  rw [integral_weightedDiffusion_sq_of_L2_domain hφ hf hc hL hG]
  exact add_le_add le_rfl hb

end KLS
end

#print axioms KLS.integrable_bochner_terms_of_diffusion_domain
#print axioms KLS.memLp_coordinateHessian_of_integrable_hessianSquare

#print axioms KLS.integral_weightedDiffusion_sq_of_L2_domain

#print axioms KLS.integral_hessianSquare_add_curvature_gradient_le_diffusion_sq
