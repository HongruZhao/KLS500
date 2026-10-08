import KLS.CumulantBounds

/-! Bounded genuine derivatives of covariance as an observable of augmented
(time,state) coordinates. The bounds come from the original compact support. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
noncomputable section
namespace KLS.StandardLocalization
open KLS.FiniteFeatureTilt
variable {n : ℕ}

def augmentedCovariance (μ : Measure (Space n)) (i j : Fin n)
    (z : Fin (n + 1) → ℝ) : ℝ := covariance μ (z 0) (Fin.tail z) i j

def augmentedScore (v : Fin (n + 1) → ℝ) (x : Space n) : ℝ :=
  score v (localizationFeature x)

theorem continuous_augmentedScore (v : Fin (n + 1) → ℝ) : Continuous (augmentedScore v) :=
  (continuous_score v).comp continuous_localizationFeature

theorem augmented_exponent_eq_score (z : Fin (n + 1) → ℝ) (x : Space n) :
    exponent (z 0) (Fin.tail z) x = augmentedScore z x := by
  rw [exponent_eq_feature_inner]
  simp only [localizationParameter, Fin.cons_self_tail, inner_toSpace_eq, augmentedScore, score]

theorem augmented_exponent_line (z v : Fin (n + 1) → ℝ) (u : ℝ) :
    exponent ((z + u • v) 0) (Fin.tail (z + u • v)) =
      fun x => exponent (z 0) (Fin.tail z) x + u * augmentedScore v x := by
  funext x
  rw [augmented_exponent_eq_score (z + u • v), augmented_exponent_eq_score z]
  simp only [augmentedScore, score, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]

def featureRadius (n : ℕ) (R : ℝ) : ℝ := Real.sqrt ((n + 1 : ℕ) : ℝ) * (R ^ 2 / 2 + R)

def covarianceDerivativeBound (n : ℕ) (R : ℝ) : ℝ :=
  8 * R ^ 2 * (Real.sqrt ((n + 1 : ℕ) : ℝ) * featureRadius n R)

theorem featureRadius_nonneg {R : ℝ} (hR : 0 ≤ R) : 0 ≤ featureRadius n R := by
  unfold featureRadius
  positivity

theorem covarianceDerivativeBound_nonneg {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ covarianceDerivativeBound n R := by
  unfold covarianceDerivativeBound
  exact mul_nonneg (by positivity) (mul_nonneg (Real.sqrt_nonneg _) (featureRadius_nonneg hR))

theorem norm_localizationFeature_le {R : ℝ} (hR0 : 0 ≤ R) (x : Space n) (hx : ‖x‖ ≤ R) :
    ‖localizationFeature x‖ ≤ featureRadius n R := by
  have hp : ‖(Fin.cons (-‖x‖ ^ 2 / 2) (fun i : Fin n => x i) : Fin (n + 1) → ℝ)‖ ≤ R ^ 2 / 2 + R := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero, Real.norm_eq_abs, abs_div, abs_neg, abs_pow,
        abs_of_nonneg (norm_nonneg x), abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have hs := pow_le_pow_left₀ (norm_nonneg x) hx 2
      linarith
    · simp only [Fin.cons_succ]
      have hc := (PiLp.norm_apply_le x j).trans hx
      nlinarith [sq_nonneg R]
  exact (norm_toSpace_le _).trans (mul_le_mul_of_nonneg_left hp (Real.sqrt_nonneg _))

theorem abs_augmentedScore_le {R : ℝ} (hR0 : 0 ≤ R)
    (v : Fin (n + 1) → ℝ) (x : Space n) (hx : ‖x‖ ≤ R) :
    |augmentedScore v x| ≤
      (Real.sqrt ((n + 1 : ℕ) : ℝ) * featureRadius n R) * ‖v‖ := by
  have h := abs_score_le (featureRadius_nonneg hR0) v (localizationFeature x)
    (norm_localizationFeature_le hR0 x hx)
  calc _ ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) * ‖v‖ * featureRadius n R := h
    _ = _ := by ring

variable {μ : Measure (Space n)} [IsProbabilityMeasure μ]

theorem contDiff_augmentedCovariance (hμ : IsCompact μ.support) (i j : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (augmentedCovariance μ i j) := by
  have hp : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin (n + 1) → ℝ => (z 0, Fin.tail z)) := by
    apply (contDiff_apply ℝ ℝ (0 : Fin (n + 1))).prodMk
    apply contDiff_pi.mpr
    intro k
    exact contDiff_apply ℝ ℝ k.succ
  convert (contDiff_covariance hμ i j).comp hp using 1
  funext z
  rfl

theorem hasDerivAt_augmentedCovariance_line (hμ : IsCompact μ.support)
    (i j : Fin n) (z v : Fin (n + 1) → ℝ) (u : ℝ) :
    HasDerivAt (fun s => augmentedCovariance μ i j (z + s • v))
      (tiltThirdCumulant μ (exponent ((z + u • v) 0) (Fin.tail (z + u • v)))
        (fun x => x i) (fun x => x j) (augmentedScore v)) u := by
  have h := hasDerivAt_tilted_covariance hμ (continuous_exponent_state (z 0) (Fin.tail z))
    (f := fun x => x i) (g := fun x => x j) (by fun_prop) (by fun_prop)
    (continuous_augmentedScore v) u
  simpa only [augmentedCovariance, covariance, law, augmented_exponent_line] using h

theorem norm_augmentedCovariance_line_deriv_le (hμ : IsCompact μ.support)
    {R : ℝ} (hR0 : 0 ≤ R) (hR : ∀ x ∈ μ.support, ‖x‖ ≤ R)
    (i j : Fin n) (z v : Fin (n + 1) → ℝ) :
    ‖tiltThirdCumulant μ (exponent (z 0) (Fin.tail z))
      (fun x => x i) (fun x => x j) (augmentedScore v)‖ ≤
      covarianceDerivativeBound n R * ‖v‖ := by
  have hb (k : Fin n) : ∀ᵐ x ∂μ.tilted (exponent (z 0) (Fin.tail z)), ‖x k‖ ≤ R :=
    (ae_norm_le hμ hR (z 0) (Fin.tail z)).mono fun x hx => (PiLp.norm_apply_le x k).trans hx
  have hs : ∀ᵐ x ∂μ.tilted (exponent (z 0) (Fin.tail z)), ‖augmentedScore v x‖ ≤
      (Real.sqrt ((n + 1 : ℕ) : ℝ) * featureRadius n R) * ‖v‖ := by
    filter_upwards [ae_norm_le hμ hR (z 0) (Fin.tail z)] with x hx
    simpa only [Real.norm_eq_abs] using abs_augmentedScore_le hR0 v x hx
  have h := norm_tiltThirdCumulant_le_of_bounds hμ
    (continuous_exponent_state (z 0) (Fin.tail z)) hR0 hR0
    (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (featureRadius_nonneg hR0)) (norm_nonneg _))
    (hb i) (hb j) hs
  calc _ ≤ 8 * R * R * ((Real.sqrt ((n + 1 : ℕ) : ℝ) * featureRadius n R) * ‖v‖) := h
    _ = _ := by unfold covarianceDerivativeBound; ring

theorem norm_augmentedCovariance_sub_le (hμ : IsCompact μ.support)
    {R : ℝ} (hR0 : 0 ≤ R) (hR : ∀ x ∈ μ.support, ‖x‖ ≤ R)
    (i j : Fin n) (z₁ z₂ : Fin (n + 1) → ℝ) :
    ‖augmentedCovariance μ i j z₁ - augmentedCovariance μ i j z₂‖ ≤
      covarianceDerivativeBound n R * ‖z₁ - z₂‖ := by
  have hd (u : ℝ) := hasDerivAt_augmentedCovariance_line hμ i j z₂ (z₁ - z₂) u
  have hb (u : ℝ) := norm_augmentedCovariance_line_deriv_le hμ hR0 hR i j
    (z₂ + u • (z₁ - z₂)) (z₁ - z₂)
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun u _ => (hd u).hasDerivWithinAt) (fun u _ => hb u)
  simpa only [one_smul, zero_smul, add_zero, add_sub_cancel] using h

def covarianceGradient (μ : Measure (Space n)) (i j : Fin n) :
    (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] ℝ :=
  fderiv ℝ (augmentedCovariance μ i j)

def covarianceHessian (μ : Measure (Space n)) (i j : Fin n) :
    (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) →L[ℝ] ℝ :=
  fderiv ℝ (covarianceGradient μ i j)

theorem hasFDerivAt_augmentedCovariance (hμ : IsCompact μ.support)
    (i j : Fin n) (z : Fin (n + 1) → ℝ) :
    HasFDerivAt (augmentedCovariance μ i j) (covarianceGradient μ i j z) z :=
  ((contDiff_augmentedCovariance hμ i j).differentiable (by simp) z).hasFDerivAt

theorem contDiff_covarianceGradient (hμ : IsCompact μ.support) (i j : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (covarianceGradient μ i j) :=
  (contDiff_augmentedCovariance hμ i j).fderiv_right (by simp)

theorem hasFDerivAt_covarianceGradient (hμ : IsCompact μ.support)
    (i j : Fin n) (z : Fin (n + 1) → ℝ) :
    HasFDerivAt (covarianceGradient μ i j) (covarianceHessian μ i j z) z :=
  ((contDiff_covarianceGradient hμ i j).differentiable (by simp) z).hasFDerivAt

theorem norm_covarianceGradient_le (hμ : IsCompact μ.support)
    {R : ℝ} (hR0 : 0 ≤ R) (hR : ∀ x ∈ μ.support, ‖x‖ ≤ R)
    (i j : Fin n) (z : Fin (n + 1) → ℝ) :
    ‖covarianceGradient μ i j z‖ ≤ covarianceDerivativeBound n R :=
  norm_fderiv_le_of_lip' ℝ (covarianceDerivativeBound_nonneg hR0)
    (Eventually.of_forall fun w => norm_augmentedCovariance_sub_le hμ hR0 hR i j w z)

end KLS.StandardLocalization
end
#print axioms KLS.StandardLocalization.hasDerivAt_augmentedCovariance_line
#print axioms KLS.StandardLocalization.hasFDerivAt_covarianceGradient
#print axioms KLS.StandardLocalization.norm_covarianceGradient_le
